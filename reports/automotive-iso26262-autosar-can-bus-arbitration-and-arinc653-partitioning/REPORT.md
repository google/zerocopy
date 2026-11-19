# Automotive ISO 26262, AUTOSAR E2E, CAN Bus Arbitration & Bus-Off Attacks, and ARINC 653 Partitioning

## Summary

Safety-critical vehicular (`ISO 26262` / `AUTOSAR` / `CAN` / `CAN-FD`) and avionics (`ARINC 653` / `AMC 20-193`) systems fail most catastrophically at the boundaries between idealized software abstractions and physical hardware/bus mechanics:

1. **Tindell's Classical CAN WCRT Equation Is Unsound (Refuted & Repaired by Davis et al. 2007):** Checking only the first instance ($q = 0$) of a message inside a critical-instant level-$m$ busy period misses **push-through interference** across successive queued instances ($q = 0, \dots, Q_m - 1$). On a realistic 500 kbit/s CAN 2.0A implicit-deadline set ($D_B = T_B = 1150\,\mu\text{s}$, $U = 96.4\%$), Tindell's formula certifies $R_B = 1000\,\mu\text{s} \le 1150\,\mu\text{s}$ (false pass), whereas Davis et al.'s busy-period equation and a discrete-event bus simulator both establish a real deadline miss at $R_B(1) = 1200\,\mu\text{s} > 1150\,\mu\text{s}$. Furthermore, direct inspection of `linux-can/can-utils` (`canframelen.c:259-270`) reveals that its `CAN-FD` length estimator misclassifies 16-byte payloads as CRC-21 (`len >= 16` instead of normative ISO 11898-1:2015 `len > 16`), omits DLC/ESI/Stuff-Count/Fixed-Stuff-Bits, and underestimates exact worst-case `CAN-FD` frame length by **4–9 bits**.
2. **ISO 11898-1 Fault Confinement Enables Manufacturer-Agnostic CAN Bus-Off Muting (Cho & Shin, CCS 2016):** CAN's Transmit Error Counter (`TEC`) transitions nodes through Error Active ($0..127$), Error Passive ($128..255$), and Bus-Off ($\ge 256$). By injecting synchronized same-ID frames with a dominant `0` bit colliding against a victim's recessive `1` bit, an adversary escalates the victim in **Stage 1** (`16` collisions $\to \text{TEC} = 128$, Error Passive) and exploits the **Passive Error Flag asymmetry** in **Stage 2** (victim's 6 recessive bits cannot corrupt the adversary's dominant bits, so the adversary's frame completes with $\text{TEC}_{\text{adv}} \mathrel{-}= 1$ while $\text{TEC}_{\text{vic}} \mathrel{+}= 8$), silencing the victim ECU into Bus-Off in **32 collisions (~5.44 ms at 500 kbit/s)**—completely bypassing message authentication codes (MACs) and `AUTOSAR E2E`.
3. **ARINC 653 Cyclic Partition Windows Do Not Isolate Shared Microarchitectural State (`POK`, `AMC 20-193`):** ARINC 653 enforces deterministic Major Frame (`MAF`) cyclic partition scheduling and bounded inter-partition sampling/queuing ports. However, direct inspection of `pok-kernel/pok` (`kernel/arch/x86/space.c:47-54`) confirms that partition switching merely flips x86 GDT segment descriptors with zero L2/LLC cache flush, cache coloring, or DRAM bandwidth policing—exposing high-criticality partitions to Cache-Related Preemption Delay (CRPD) and multicore DRAM bank/row-buffer interference that can violate partition time windows unless mitigated under `AMC 20-193` / `AC 20-193` (e.g., cache way partitioning + `MemGuard`). Source inspection of `pok` also surfaced concrete kernel defects (`portsamplingread.c:61-65`: indexing `pok_ports` by partition ID instead of port ID and leaking the port spinlock on invalid-pointer error return).
4. **ISO 26262 ASIL Decomposition Does Not Relax Random Hardware Metrics and Breaks Under Common-Cause Coupling:** Decomposing an `ASIL D` requirement into `ASIL B(D) + ASIL B(D)` reduces systematic software rigor only if Dependent Failure Analysis (`DFA`, ISO 26262-9 Clause 7) establishes **Sufficient Independence** (no cascading or Common-Cause Failures). Hardware architectural targets (`SPFM >= 99%`, `LFM >= 90%`, `PMHF < 10 FIT`) remain pinned to the parent `ASIL D` safety goal; even modest $\beta \ge 12.5\%$ common-cause coupling across two 80-FIT channels pushes system PMHF past the 10-FIT `ASIL D` ceiling regardless of dual-channel redundancy. `AUTOSAR E2E` profiles (`1, 4, 5, 6, 7, 11, 22`) provide runtime Freedom From Interference (`FFI`) over communication faults (corruption, loss, delay, repetition, masquerading) but cannot defend against physical/data-link Bus-Off muting without timeout-driven fail-safe fallback.

## Applicability

This report combines normative automotive and avionics standards, peer-reviewed verification and attack analyses, direct source inspection of three pinned upstream repositories, and four standalone executable micro-probes:

- **CAN / CAN-FD Frame Timing, Error Counters, and Bus-Off Handling:**
  - `linux-can/can-utils` @ `834ceef1f1eabec67625389172eebf1050d2f42b` (`canframelen.c`, `canbusload.c`, `include/linux/can/error.h`): applies to userspace Linux SocketCAN bus-load estimation and error-frame decoding for Classical CAN (`CAN_MTU`) and CAN-FD (`CANFD_MTU`).
  - `torvalds/linux` @ `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd` (`drivers/net/can/dev/dev.c`, `include/uapi/linux/can/error.h`): applies to Linux kernel SocketCAN error-state transitions (`CAN_ERROR_WARNING_THRESHOLD = 96`, `CAN_ERROR_PASSIVE_THRESHOLD = 128`, `CAN_BUS_OFF_THRESHOLD = 256`) and Bus-Off recovery (`restart_ms` automatic timer vs. manual `can_restart_now`).
  - `ISO 11898-1:2015`, Davis et al. (2007), and Cho & Shin (CCS 2016): apply to priority-arbitrated non-preemptive CAN 2.0A/2.0B and CAN-FD networks using standard wired-AND dominant/recessive signaling and ISO 11898-1 fault confinement.
- **Avionics Integrated Modular Avionics (IMA) Time/Space Partitioning:**
  - `pok-kernel/pok` @ `b2e1cc382f86adba47cb93f015d92bc2d11cf40e` (`kernel/core/sched.c`, `kernel/arch/x86/space.c`, `kernel/middleware/portsamplingread.c`, `kernel/middleware/portsamplingwrite.c`, `libpok/arinc653/sampling.c`, `libpok/arinc653/queueing.c`): applies to an open-source ARINC 653-like partitioned OS targeting x86 (single-core and global-rendezvous SMP).
  - `ARINC 653P1`, `EASA AMC 20-193` / `FAA AC 20-193` (replacing `CAST-32A`), `MemGuard` (Yun et al. 2013), and `Nowotsch et al.` (2014): apply to single-core and multi-core IMA airborne platforms targeting `DO-178C` DAL A–C certification.
- **Automotive Functional Safety & End-to-End Protection:**
  - `ISO 26262:2018` (Parts 5, 6, 9) and `AUTOSAR_PRS_E2EProtocol`: apply to road-vehicle E/E systems (ASIL A–D, QM coexistence, mixed-criticality ECU partitioning, and E2E-protected inter-ECU / inter-partition PDUs).

**Relationship Among Subjects:** The automotive and avionics stacks confront the same core verification problem—**compositional isolation of mixed-criticality software sharing deterministic hardware fabrics**—from two complementary angles. Avionics (`ARINC 653` + `AMC 20-193`) centers on static cyclic time-space partitioning and bounded multicore hardware interference (`MCP_Resource_Usage`), while automotive (`ISO 26262` + `AUTOSAR E2E` + `CAN`) pairs ASIL decomposition and runtime end-to-end fault detection with fixed-priority non-preemptive shared bus arbitration.

## Findings

### 1. CAN / CAN-FD Priority Arbitration Timing: Refuting Tindell and Auditing `can-utils`

Basis: normative (`ISO 11898-1:2015`; Davis, Burns, Bril, Lukkien, Real-Time Systems 2007, DOI `10.1007/s11241-007-9012-7`) + source (`linux-can/can-utils` @ `834ceef1f1eabec67625389172eebf1050d2f42b`, `canframelen.c`, `canbusload.c`) + execution (`Probe 2A`).

#### 1.1 Exact Classical CAN vs. CAN-FD Bit-Stuffing Frame Length Bounds

On Classical CAN (`ISO 11898-1`), bit stuffing inserts an inverted stuff bit after every 5 consecutive identical bits across the stuffed region (`SOF` through `CRC`). Because the inserted stuff bit itself starts a run of length 1 of the opposite polarity, each subsequent stuff bit requires only 4 original bits, giving at most $\lfloor (N_{\text{stuffed}} - 1) / 4 \rfloor$ stuff bits:

- **Classical CAN 2.0A (11-bit Standard ID, payload $s \in \{0..8\}$ bytes):**
  - Unstuffed total (including 3-bit Intermission/IFS): $1\text{ (SOF)} + 11\text{ (ID)} + 1\text{ (RTR)} + 1\text{ (IDE)} + 1\text{ (r0)} + 4\text{ (DLC)} + 8s\text{ (Data)} + 15\text{ (CRC)} + 1\text{ (CRCdel)} + 1\text{ (ACK)} + 1\text{ (ACKdel)} + 7\text{ (EOF)} + 3\text{ (IFS)} = 47 + 8s\text{ bits}$.
  - Stuffed span: $34 + 8s$ bits $\implies$ max stuff bits $\lfloor (34 + 8s - 1)/4 \rfloor = 8 + 2s$.
  - Worst-case wire length: $C_m = (55 + 10s)\,\tau_{\text{bit}}$ (`135` bits = `270 us` for an 8-byte frame at 500 kbit/s). Confirmed in `canframelen.c:276-278`: `CFL_NO_BITSTUFFING = 47 + 8*len`, `CFL_WORSTCASE = 55 + 10*len`.
- **Classical CAN 2.0B (29-bit Extended ID):** Adds 18 ID bits + `SRR` + `r1` (+20 bits in the stuffed region), giving $67 + 8s$ unstuffed and $80 + 10s$ worst-case bits (`canframelen.c:276-278`).
- **CAN-FD (`ISO 11898-1:2015`, 11-bit FBFF, payload $D \in \{0..8, 12, 16, 20, 24, 32, 48, 64\}$ bytes):**
  - Dynamic bit stuffing applies strictly from `SOF` through the end of `Data` ($22 + 8D$ bits: `1 SOF + 11 ID + 1 RRS + 1 IDE + 1 FDF + 1 res + 1 BRS + 1 ESI + 4 DLC + 8D`). Because `RRS=0, IDE=0, FDF=1, res=0` forces a polarity transition inside the header, exact dynamic programming (`Probe 2A-ii`) proves the tight maximum dynamic stuff-bit count is **$4 + 2D$** (1 bit tighter than the unconstrained bound $\lfloor(21+8D)/4\rfloor = 5 + 2D$).
  - To eliminate undetected bit-stuffing errors in high-speed data phases, `ISO 11898-1:2015` replaces dynamic stuffing in the CRC region with a **4-bit Stuff Count** (3-bit Gray-coded `stuff_count mod 8` + 1 even parity bit), a payload-tiered CRC (**CRC-17 for $D \le 16$ bytes**, **CRC-21 for $D > 16$ bytes**), and **Fixed Stuff Bits (FSB)** inserted deterministically before the stuff count and after every 4 bits (**6 FSB** for CRC-17 $\implies$ 27-bit CRC block; **7 FSB** for CRC-21 $\implies$ 32-bit CRC block), followed by a 13-bit unstuffed trailer (`CRCdel + ACK + ACKdel + 7 EOF + 3 IFS`).
  - Under Bit Rate Switch (`BRS = 1`), wire transmission time splits at the `BRS` sample point through the `CRCdel` sample point: $C_m^{\text{FD}} = N_{\text{arb}}\,\tau_{\text{arb}} + N_{\text{data}}\,\tau_{\text{data}}$.

#### 1.2 Upstream Source Discrepancy in `linux-can/can-utils` (`canframelen.c:239-270`)

Direct inspection of `canframelen.c` (`834ceef1f1eabec67625389172eebf1050d2f42b`, called by `canbusload.c:131` defaulting to `CFL_WORSTCASE`) exposes **four concrete bugs** in its `CAN-FD` estimator (prefaced by the author's comment `/* not correct, but close ? */`, line 260):

1. **Off-by-one CRC-17/CRC-21 boundary (`canframelen.c:246, 263`):** Uses `(frame->len >= 16) ? 21 : 17`, misclassifying **16-byte CAN-FD frames** as CRC-21 instead of ISO 11898-1:2015 CRC-17.
2. **Omitted header and CRC-block fields (`canframelen.c:263-265`):** Computes `1 + 11 + crc + 5 + 12 + 8*len`, omitting 4-bit `DLC`, 1-bit `ESI`, 4-bit `Stuff Count`, `6`/`7` `Fixed Stuff Bits`, and merging `BRS` and `CRCdel` into 1 bit—undercounting unstuffed FBFF length by 16 bits ($D \le 12$), 12 bits ($D = 16$), and 17 bits ($D \ge 20$).
3. **Crude `5 / 4` worst-case multiplier (`canframelen.c:249, 267`):** Multiplies the entire unstuffed length (including unstuffed trailer and fixed-stuff CRC) by `5/4`, yet still **underestimates** exact ISO 11898-1:2015 worst-case FBFF length across all payload sizes (`Probe 2A-ii`):

| Payload $D$ (bytes) | ISO CRC | `can-utils` CRC | ISO Unstuffed (bits) | `can-utils` Unstuffed | ISO Exact Worst-Case (bits) | `can-utils` `5/4` (bits) | Error (`can-utils` $-$ ISO) |
| :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| 0 | 17 | 17 | 62 | 46 | **66** | 57 | **$-9$ bits** |
| 8 | 17 | 17 | 126 | 110 | **146** | 137 | **$-9$ bits** |
| 12 | 17 | 17 | 158 | 142 | **186** | 177 | **$-9$ bits** |
| **16** | **17** | **21 (bug)** | **190** | **178** | **226** | **222** | **$-4$ bits** |
| 20 | 21 | 21 | 227 | 210 | **271** | 262 | **$-9$ bits** |
| 32 | 21 | 21 | 323 | 306 | **391** | 382 | **$-9$ bits** |
| 64 | 21 | 21 | 579 | 562 | **711** | 702 | **$-9$ bits** |

4. **Unsupported exact mode (`canframelen.c:268-269`):** `CFL_EXACT` returns `0` for `CANFD_MTU` (`/* exact bittiming for CANFD not supported yet */`). Using `canbusload` or `can_frame_length` for safety-critical CAN-FD schedulability input is therefore **unsafe**.

#### 1.3 Tindell's Flawed WCRT Equation vs. Davis et al.'s (2007) Busy-Period Revision

Because CAN arbitration is **fixed-priority non-preemptive** (lowest CAN ID wins arbitration at Start-of-Frame, and once transmitted a frame cannot be preempted), a message $m$ with period $T_m$, relative deadline $D_m$, worst-case transmission time $C_m$, and queuing jitter $J_m$ can suffer at most one lower-priority blocking frame $B_m = \max_{k \in lp(m)} C_k$.

- **Tindell et al. (1994/1995) — Flawed Single-Instance Formula:** Assumed the worst-case response time always occurs for the *first* instance ($q = 0$) queued at the critical instant:
  $$w_m^{n+1} = B_m + \sum_{j \in hp(m)} \left\lceil \frac{w_m^n + J_j + \tau_{\text{bit}}}{T_j} \right\rceil C_j, \qquad R_m^{\text{Tindell}} = J_m + w_m + C_m$$
- **Why Tindell Fails (Push-Through Interference):** Even when $R_m(0) \le D_m \le T_m$, higher-priority messages released *while* $m$'s instance $q = 0$ is transmitting non-preemptively are deferred until $m(0)$ finishes. Their deferred execution can extend the priority-level-$m$ busy period **past $T_m$**, colliding with instance $q = 1$ (and subsequent instances) and triggering additional higher-priority arrivals that cause $R_m(q) > R_m(0)$!
- **Davis, Burns, Bril, and Lukkien (2007) — Exact Level-$m$ Busy-Period Revision:**
  1. Compute the longest **priority-level-$m$ busy period** $t_m$ (starting from $t_m^0 = C_m$):
     $$t_m^{n+1} = B_m + \sum_{j \in hep(m)} \left\lceil \frac{t_m^n + J_j}{T_j} \right\rceil C_j$$
  2. Count all instances of $m$ released inside the busy period:
     $$Q_m = \left\lceil \frac{t_m + J_m}{T_m} \right\rceil$$
  3. For every instance $q \in \{0, 1, \dots, Q_m - 1\}$, solve the fixed-point queuing delay $w_m(q)$ (starting from $w_m^0(q) = B_m + q C_m$):
     $$w_m^{n+1}(q) = B_m + q C_m + \sum_{j \in hp(m)} \left\lceil \frac{w_m^n(q) + J_j + \tau_{\text{bit}}}{T_j} \right\rceil C_j$$
  4. Take the worst response time across **all** $Q_m$ instances:
     $$R_m(q) = J_m + w_m(q) - q T_m + C_m, \qquad R_m = \max_{0 \le q < Q_m} R_m(q)$$
  - Davis et al. (2007) also refuted the belief that Deadline-Minus-Jitter ($D_m - J_m$) Monotonic priority ordering is optimal on CAN, showing Audsley's Optimal Priority Assignment (`OPA`) algorithm is required instead.

**Execution Verification (`Probe 2A`):** On a 4-message 500 kbit/s CAN 2.0A set with implicit deadlines ($D_m = T_m$, $\tau_{\text{bit}} = 2\,\mu\text{s}$, utilization $U = 96.43\%$): $m_1, m_2$ (8 B, $C = 270\,\mu\text{s}$, $T = 750\,\mu\text{s}$), $m_B$ (8 B, $C = 270\,\mu\text{s}$, $T = D = 1150\,\mu\text{s}$), and low-priority blocker $m_L$ (4 B, $C = 190\,\mu\text{s}$, $T = 20000\,\mu\text{s}$):

- **Tindell ($q=0$ only):** $w_B = 730\,\mu\text{s} \implies R_B^{\text{Tindell}} = 1000\,\mu\text{s} \le 1150\,\mu\text{s}$ (**FALSE PASS**).
- **Davis et al. (2007):** Busy period $t_B = 6670\,\mu\text{s}$, $Q_B = 6$ instances with $R_B(q) = [1000, \mathbf{1200}, 860, 520, 720, 380]\,\mu\text{s} \implies R_B = \mathbf{1200\,\mu\text{s}} > 1150\,\mu\text{s}$ (**DEADLINE MISS on $q = 1$**).
- **Discrete-Event Non-Preemptive Bus Simulator:** Observes exact worst-case response time **`1200 us` on instance `q = 1`**, confirming that Davis et al.'s bound is physically realized on the wire.

---

### 2. CAN Error Confinement and Cho & Shin's Bus-Off ECU Muting Attack

Basis: normative (`ISO 11898-1:2015`; Cho & Shin, ACM CCS 2016, DOI `10.1145/2976749.2978360`) + source (`torvalds/linux` @ `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`, `include/uapi/linux/can/error.h`, `drivers/net/can/dev/dev.c`) + execution (`Probe 2B`).

#### 2.1 ISO 11898-1 Fault Confinement State Machine & SocketCAN Implementation

Every compliant CAN controller maintains an 8-bit Receive Error Counter (`REC`) and Transmit Error Counter (`TEC`). Linux SocketCAN codifies the exact ISO 11898-1 thresholds in `include/uapi/linux/can/error.h:139-141` and `drivers/net/can/dev/dev.c:134-144`:

| Error State | Counter Range | Error Flag Emitted on Fault | Post-TX Delay | Linux SocketCAN Symbol (`error.h` / `dev.c`) |
| :--- | :---: | :--- | :--- | :--- |
| **Error Active** | $\text{TEC} < 96$ (and $\text{REC} < 96$) | Active Error Flag (**6 dominant `0` bits**) — destroys current frame bus-wide | 3-bit Intermission (IFS) | `CAN_STATE_ERROR_ACTIVE` |
| **Error Warning** (implementation status) | $96 \le \max(\text{TEC}, \text{REC}) \le 127$ | Active Error Flag (**6 dominant `0` bits**) | 3-bit IFS | `CAN_ERROR_WARNING_THRESHOLD = 96` |
| **Error Passive** | $128 \le \max(\text{TEC}, \text{REC}) \le 255$ | Passive Error Flag (**6 recessive `1` bits**) — **cannot override dominant bits** | 3-bit IFS + **8-bit Suspend Transmission** after successful TX | `CAN_ERROR_PASSIVE_THRESHOLD = 128` |
| **Bus-Off** | $\text{TEC} \ge 256$ | None — TX driver physically disconnected from bus | Recovery requires `128 × 11 = 1408` recessive bits (or controller reset) | `CAN_BUS_OFF_THRESHOLD = 256`, `can_bus_off()` (`dev.c:264-280`) |

Error counter update rules (standard transmit case): a detected transmit error (e.g., Bit Error when transmitting recessive `1` but sampling dominant `0` outside arbitration) increments $\text{TEC} \mathrel{+}= 8$; a successful transmission decrements $\text{TEC} \mathrel{-}= 1$ (down to `0`).

#### 2.2 Two-Stage Bus-Off Attack Mechanics (Cho & Shin, CCS 2016)

An adversary controlling any compromised peripheral ECU on the CAN bus (requiring zero knowledge of proprietary payload semantics and defeating application-layer MACs/`AUTOSAR E2E`) exploits the **Active vs. Passive Error Flag asymmetry** in two stages:

1. **Synchronization Trigger:** The adversary waits for an antecedent periodic frame (or fixed inter-arrival period) and starts transmitting a crafted frame with the **exact same CAN ID** as the victim ECU at the exact same `SOF` edge, tying arbitration bit-for-bit. At the first bit position after arbitration (e.g., `DLC` or first data bit) where the victim transmits recessive `1`, the adversary transmits dominant `0`.
2. **Stage 1 — Escalation to Error Passive (`Collisions #1..#16`):**
   - The victim monitors the bus, reads dominant `0` instead of its recessive `1`, detects a **Bit Error**, aborts, increments $\text{TEC}_{\text{vic}} \mathrel{+}= 8$, and emits a **6-dominant-bit Active Error Flag**.
   - The victim's Active Error Flag violates bit stuffing on the adversary's ongoing frame; the adversary detects a **Stuff Error** and also increments $\text{TEC}_{\text{adv}} \mathrel{+}= 8$.
   - After **16 consecutive collisions** (from $\text{TEC}=0$), both reach $\text{TEC} = 128$ and transition to **Error Passive**.
3. **Stage 2 — Asymmetric Passive-Flag Escalation to Bus-Off (`Collisions #17..#32`):**
   - Because the victim is now **Error Passive**, when the next collision induces a Bit Error ($\text{TEC}_{\text{vic}} \mathrel{+}= 8$), the victim emits a **Passive Error Flag (6 recessive `1` bits)**.
   - Under CAN's wired-AND physical layer, recessive bits yield silently to the adversary's dominant bits! The adversary's frame **completes uncorrupted and receives ACK** from healthy receivers, decrementing $\text{TEC}_{\text{adv}} \mathrel{-}= 1$ (dropping the adversary immediately back below `128` into Error Warning/Active!), while the victim's automatic hardware retransmission collides again until $\text{TEC}_{\text{vic}}$ hits **`256` (Bus-Off)** on Collision #32!

**Execution Verification (`Probe 2B`):** Simulating the exact ISO 11898-1 TEC state machine confirms:
- Collision `#12`: Victim `TEC=96 [ERROR_WARNING]`, Adversary `TEC=96 [ERROR_WARNING]`.
- Collision `#16`: Victim `TEC=128 [ERROR_PASSIVE]`, Adversary `TEC=128 [ERROR_PASSIVE]`.
- Collision `#17`: Victim `TEC=136 [ERROR_PASSIVE]`, Adversary `TEC=127 [ERROR_WARNING]` (asymmetry activates).
- Collision `#32`: Victim `TEC=256 [BUS_OFF]`, Adversary `TEC=112 [ERROR_WARNING]` (adversary stays healthy and operational!).
- Total muting latency at 500 kbit/s: **~5.44 ms** (below a single 10 ms automotive control loop tick!).
- Furthermore, in Linux SocketCAN (`drivers/net/can/dev/dev.c:241-280`), if `priv->restart_ms == 0` (the default unless explicitly configured via `ip link set can0 type can restart-ms <N>`), `can_bus_off()` calls `netif_carrier_off(dev)` and **never automatically recovers** without explicit userspace intervention (`can_restart_now`). Even if automatic recovery is enabled, an adversary can re-mute the victim every `restart_ms + 5.44 ms`, achieving persistent targeted DoS. Follow-up work (`WeepingCAN`, Bloom, AutoSec/NDSS 2021; `Serag et al.`, USENIX Security 2021) demonstrated stealthier single-frame / passive-error-regeneration variants that avoid consecutive-collision IDS signatures.

---

### 3. ARINC 653 Cyclic Partitioning vs. Shared Cache/DRAM Microarchitectural State

Basis: normative (`ARINC 653P1`; `EASA AMC 20-193` / `FAA AC 20-193`, superseding `CAST-32A`; Yun et al., RTAS 2013; Nowotsch et al., ECRTS 2014) + source (`pok-kernel/pok` @ `b2e1cc382f86adba47cb93f015d92bc2d11cf40e`) + execution (`Probe 2C`).

#### 3.1 ARINC 653 Time/Space Partitioning and APEX Communication Semantics

ARINC 653 Part 1 defines the **APEX (APplication EXecutive)** interface for Integrated Modular Avionics (IMA) so multiple software applications of different Design Assurance Levels (DAL A–E under `DO-178C`) share one computing module with strict logical isolation:

- **Two-Level Hierarchical Scheduling:**
  - *Module level (static cyclic):* Time is divided into a repeating **Major Time Frame (MAF)** partitioned into fixed-duration **Partition Time Windows (slots)** allocated offline to specific partitions. `pok-kernel/pok` (`kernel/core/sched.c:96-123`) explicitly checks the conservation invariant $\sum_{i=0}^{N-1} \text{pok\_sched\_slots}[i] == \text{POK\_CONFIG\_SCHEDULING\_MAJOR\_FRAME}$ at boot and triggers `POK_ERROR_KIND_KERNEL_CONFIG` on mismatch.
  - *Partition level (preemptive priority):* Inside its window, each partition schedules its own internal processes (e.g., fixed-priority or RMS in `pok_elect_thread`, `sched.c:188-287`) with per-process `time_capacity` and `period` budgets.
- **Inter-Partition Communication Ports (`libpok/arinc653/{sampling,queueing}.c`):**
  - **Sampling Ports:** Single-buffer overwrite semantics (`WRITE_SAMPLING_MESSAGE` overwrites the slot; `READ_SAMPLING_MESSAGE` returns the latest sample non-destructively along with a `VALIDITY` flag computed against `REFRESH_PERIOD`, verified in `portsamplingread.c:77-81`: `(last_receive + refresh) < POK_GETTICK() ? FALSE : TRUE`). Zero queuing unboundedness; designed for periodic sensor/state telemetry.
  - **Queuing Ports:** Bounded FIFO buffers (`MAX_NB_MESSAGE × MAX_MESSAGE_SIZE`, `queueing.c:24-71`) preserving every discrete command/event message in arrival order, returning `NOT_AVAILABLE` / blocking up to `TIME_OUT` when empty or full.
  - **Deterministic Port Flush Boundaries (`pok/kernel/core/sched.c:144-164`):** Inter-partition writes are buffered and flushed either at Major Frame boundaries (`pok_port_flushall`), partition-window exit (`POK_NEEDS_FLUSH_ON_WINDOWS`), or a fixed `POK_FLUSH_PERIOD`, preventing asynchronous cross-partition jitter.

#### 3.2 Direct Source Inspection of `pok-kernel/pok`: Logical vs. Microarchitectural Isolation & Kernel Defects

Inspecting `pok-kernel/pok` @ `b2e1cc382f86adba47cb93f015d92bc2d11cf40e` reveals both the exact microarchitectural gap highlighted by `CAST-32A` / `AMC 20-193` and concrete implementation bugs in a reference ARINC 653 kernel:

1. **Zero Microarchitectural State Scrubbing on Partition Switch (`kernel/arch/x86/space.c:47-54`):**
   ```c
   pok_ret_t pok_space_switch(uint8_t old_partition_id, uint8_t new_partition_id) {
     gdt_disable(GDT_PARTITION_CODE_SEGMENT(old_partition_id));
     gdt_disable(GDT_PARTITION_DATA_SEGMENT(old_partition_id));
     gdt_enable(GDT_PARTITION_CODE_SEGMENT(new_partition_id));
     gdt_enable(GDT_PARTITION_DATA_SEGMENT(new_partition_id));
     return (POK_ERRNO_OK);
   }
   ```
   `pok_space_switch` toggles x86 GDT segment descriptors only. It executes **no cache flush/invalidation**, **no cache way/color partitioning**, **no branch-predictor / TLB / prefetcher isolation**, and **no DRAM bank partitioning**. Even though `pok_global_sched` (`sched.c:308-341`) enforces a global multi-core rendezvous barrier (`fence` + `barr` in `synchro_processors`) so only one partition runs across all cores at a time (avoiding concurrent cross-partition execution on SMP at high utilization cost), cross-slot residual L2/LLC eviction and DRAM row-buffer state still leak timing interference across partition windows!
2. **Concrete Safety/Isolation Defects Found in POK APEX Middleware:**
   - **Wrong array index & spinlock leak (`kernel/middleware/portsamplingread.c:56-66`):** After acquiring `pok_lockobj_lock(&pok_ports[id].lock, NULL)` on line 56, line 61 computes `uint32_t sz = pok_ports[pid].size;`—indexing `pok_ports` by the **partition ID `pid`** instead of the **port ID `id`**! Worse, if `!pok_check_ptr_in_partition(pid, ptr, sz)` fails on line 63, line 64 returns `POK_ERRNO_EINVAL` **without unlocking `&pok_ports[id].lock`**, permanently deadlocking subsequent accesses to that sampling port.
   - **Broken status wrapper (`libpok/arinc653/queueing.c:117-132`):** `GET_QUEUING_PORT_STATUS` invokes `pok_port_queueing_id(QUEUING_PORT_ID, &status)` (an ID-lookup function, not a status syscall) and comments out `MAX_NB_MESSAGE` under `#warning TBSL`.

#### 3.3 Multicore Shared-Resource Interference (`AMC 20-193` / `AC 20-193`) and Quantitative Bound (`Probe 2C`)

When IMA platforms deploy concurrent multicore partitions on COTS Multi-Core Processors (MCPs), EASA `AMC 20-193` (2022) and FAA `AC 20-193` (2024)—codifying `CAST-32A`—require explicit identification and mitigation of all **Interference Channels** (`MCP_Resource_Usage` and `MCP_Software` objectives) to establish **Robust Resource and Time Partitioning**:

- **Shared L2/L3 (LLC) Cache Eviction & Coherency Traffic:** Evicting a DAL-A partition's hot working set introduces Cache-Related Preemption Delay (CRPD) and continuous capacity misses. Mitigated via hardware cache way partitioning (e.g., Intel CAT / Arm MPAM) or OS page coloring.
- **Shared DRAM Controller, Bank Conflicts, and Interconnect Bandwidth:** Concurrent memory-intensive cores cause DRAM row-buffer misses (forcing precharge + activate latency) and memory-controller queue starvation, inflating WCET by $2\times$–$10\times$ if unpoliced. Mitigated via **DRAM bank partitioning** plus **PMC-based bandwidth reservation (`MemGuard`, Yun et al. RTAS 2013)** and **interference-sensitive WCET (`isWCET`) analysis (Nowotsch et al., ECRTS 2014)**.

**Execution Verification (`Probe 2C`):** Modeling a DAL-A Flight Control partition (ARINC 653 window `8.000 ms`, `MAF = 20.0 ms`, isolated single-core WCET `6.200 ms`, `+1.800 ms` nominal margin):
- Unpartitioned LLC eviction (`4096` lines $\times 120\text{ ns}$) adds **`+0.492 ms` CRPD**.
- Three concurrent unthrottled cores causing `110 ns` average worst-case DRAM queuing/row-conflict penalty across `25,000` off-chip memory requests add **`+2.750 ms`**.
- **Unmitigated multicore WCET = `9.442 ms` $\implies$ `1.442 ms` window overrun** despite passing isolated WCET!
- Adding LLC page coloring/way-partitioning (`CRPD = 0`) + `MemGuard` policing (capping worst-case DRAM queuing to `25 ns/req` = `+0.625 ms`) restores **bounded WCET = `6.825 ms`** (`+1.175 ms` verified margin).

---

### 4. ISO 26262 ASIL Decomposition, Common-Cause Failure Laws, and AUTOSAR E2E

Basis: normative (`ISO 26262:2018` Parts 5, 6, 9; `AUTOSAR_PRS_E2EProtocol`) + execution (`Probe 2D`).

#### 4.1 ASIL Decomposition Rules (ISO 26262-9 Clause 5) and Hardware Metric Invariance (ISO 26262-5)

ISO 26262-9 Clause 5 permits decomposing a safety requirement of parent integrity level $X \in \{\text{A, B, C, D}\}$ into redundant requirements allocated to **sufficiently independent elements**, written with the parent ASIL in parentheses:

| Parent ASIL | Valid Redundant Decompositions (ISO 26262-9 Table 1) | Parent Hardware Targets (ISO 26262-5, **NOT relaxed by decomposition**) |
| :--- | :--- | :--- |
| **ASIL D** | `ASIL D(D) + QM(D)`, `ASIL C(D) + ASIL A(D)`, `ASIL B(D) + ASIL B(D)` | `SPFM >= 99%`, `LFM >= 90%`, `PMHF < 10^-8 / h` (`< 10 FIT`) |
| **ASIL C** | `ASIL C(C) + QM(C)`, `ASIL B(C) + ASIL A(C)` | `SPFM >= 97%`, `LFM >= 80%`, `PMHF < 10^-7 / h` (`< 100 FIT`) |
| **ASIL B** | `ASIL B(B) + QM(B)`, `ASIL A(B) + ASIL A(B)` | `SPFM >= 90%`, `LFM >= 60%`, `PMHF < 10^-7 / h` (`< 100 FIT`) |
| **ASIL A** | `ASIL A(A) + QM(A)` | Qualitative / safety mechanism coverage (no mandatory SPFM/LFM/PMHF numeric floor) |

**Two Load-Bearing Legal & Mathematical Constraints:**

1. **Hardware Architectural Metrics Remain Pinned to the Parent ASIL (ISO 26262-9 Clause 5.4.2):** Decomposing `ASIL D` into `ASIL B(D) + ASIL B(D)` reduces *systematic* software development rigor (e.g., MC/DC vs. branch coverage, formal methods requirements in Part 6) on each redundant channel, **not** the overall random hardware failure targets (`SPFM >= 99%`, `LFM >= 90%`, `PMHF < 10 FIT`) of the safety goal!
2. **Dependent Failure Analysis (`DFA`, ISO 26262-9 Clause 7) & Sufficient Independence:** Decomposition is **invalid** unless DFA proves absence (or sufficient control) of:
   - **Cascading Failures:** A fault in Element 1 propagates to Element 2 (e.g., QM task corrupting ASIL RAM or starving CPU/bus). Mitigated via **Freedom From Interference (`FFI`)** across **timing/execution** (MPU/watchdog/cyclic budgets), **memory** (hardware MPU/MMU spatial isolation), and **exchange of information** (`AUTOSAR E2E`).
   - **Common-Cause Failures (`CCF`):** A single root cause simultaneously defeats both redundant elements—shared power rail / clock oscillator / voltage regulator, shared silicon die thermal/EMI transient, identical systematic software bug in non-diverse code, shared compiler code-generation defect, or shared CAN transceiver/bus medium.

**Execution Verification (`Probe 2D`):** Under the standard 1oo2 $\beta$-factor model ($\text{PMHF} \approx \beta \lambda_{\text{ch}} + (1 - \beta)^2 \lambda_{\text{ch}}^2 T_{\text{life}}$) for two `ASIL B(D)` channels with $\lambda_{\text{ch}} = 80\text{ FIT}$ ($8 \times 10^{-8}\text{ h}^{-1}$) over $T_{\text{life}} = 10{,}000\text{ h}$:

| CCF Fraction $\beta$ | CCF Contribution ($\beta\lambda_{\text{ch}}$) | Independent Dual-Point Contribution | Total System PMHF | Parent ASIL D Verdict (`< 10 FIT`) |
| :---: | :---: | :---: | :---: | :--- |
| `0.0%` (ideal) | `0.00 FIT` | `0.0640 FIT` | **`0.06 FIT`** | PASS |
| `1.0%` | `0.80 FIT` | `0.0627 FIT` | **`0.86 FIT`** | PASS |
| `5.0%` | `4.00 FIT` | `0.0578 FIT` | **`4.06 FIT`** | PASS |
| `10.0%` | `8.00 FIT` | `0.0518 FIT` | **`8.05 FIT`** | PASS (marginal) |
| **`15.0%`** | **`12.00 FIT`** | `0.0462 FIT` | **`12.05 FIT`** | **FAIL (`>= 10 FIT`)** |
| **`20.0%`** | **`16.00 FIT`** | `0.0410 FIT` | **`16.04 FIT`** | **FAIL (`>= 10 FIT`)** |

Notice that once $\beta \ge 1\%$, **over 92% of total system failure risk comes from the CCF term $\beta\lambda_{\text{ch}}$**, not independent dual-channel failures—demonstrating quantitatively why an unmitigated shared clock, power domain, toolchain bug, or single CAN bus destroys the safety credit of `ASIL B(D) + ASIL B(D)` decomposition.

#### 4.2 AUTOSAR E2E Protection Profiles (`AUTOSAR_PRS_E2EProtocol`)

To establish **Freedom From Interference in exchange of information** (ISO 26262-6 / Part 9) across untrusted or lower-ASIL communication stacks (COM, PduR, CanIf, Ethernet/SOME/IP) and physical buses, `AUTOSAR E2E` wraps safety PDUs in end-to-end checked headers detecting repetition, loss, delay, insertion, masquerading, incorrect addressing, incorrect sequence, corruption, and asymmetric information:

| AUTOSAR E2E Profile | CRC Width & Polynomial | Counter Width | Data ID Handling | Length Field | Target Payload / Bus Domain |
| :--- | :--- | :---: | :--- | :---: | :--- |
| **Profile 1** (legacy) / **Profile 11** | 8-bit CRC-8-SAE J1850 (`0x1D`) | 4-bit (`0..14`) | 16-bit (`BOTH`, `ALT`, `LOW`, `NIBBLE`) implicit/partial explicit | Fixed | Classical CAN (8 B), LIN, compact signals |
| **Profile 2** / **Profile 22** | 8-bit CRC-8H2F (`0x2F`) | 4-bit (`0..15`) | 16-entry `DataIDList[16]` indexed by counter (implicit in CRC) | Fixed | Classical CAN / CAN-FD compact frames |
| **Profile 4** | 32-bit CRC-32P4 (`0xF4ACFB13`, HD=6 up to 4 KiB) | 16-bit | 32-bit **explicit** in E2E header | 16-bit explicit | CAN-FD, FlexRay, Ethernet / SOME/IP (dynamic $\le 4\text{ KiB}$) |
| **Profile 5** | 16-bit CRC-16-CCITT (`0x1021`) | 8-bit | 16-bit **implicit** (appended into CRC, not on wire) | Fixed | CAN-FD, FlexRay, Ethernet (low header overhead: 3 B) |
| **Profile 6** | 16-bit CRC-16-CCITT (`0x1021`) | 8-bit | 16-bit **implicit** | 16-bit explicit | CAN-FD, Ethernet (dynamic length, 5 B header) |
| **Profile 7** | 64-bit CRC-64-ECMA (`0x42F0E1EBA9EA3693`) | 32-bit | 32-bit **explicit** | 32-bit explicit | Automotive Ethernet / ADAS large payloads ($\le 4\text{ MiB}$, 20 B header) |

**Critical Security-Safety Boundary:** `AUTOSAR E2E` protects against **random hardware faults and systematic lower-stack software faults** (using non-cryptographic CRCs and unkeyed counters). It does **not** authenticate against deliberate malicious forgery (which requires `AUTOSAR SecOC` truncated CMAC/HMAC + freshness counters), and **neither `E2E` nor `SecOC` prevents Cho & Shin's data-link Bus-Off muting attack** (`Section 2.2`). Under a Bus-Off attack, the receiver's `E2E` state machine detects **message loss / timeout** (`E2E_PxxSTATUS_NONEWDATA`) and must transition the vehicle to a degraded fail-safe state (or switch to a physically redundant independent bus channel to satisfy CCF independence).

## Boundaries

- **Known not to apply — Classical CAN WCRT to Non-Abortable FIFO Transmit Mailboxes:** Davis et al.'s (2007) equations assume hardware transmit buffers are strictly priority-ordered (or abortable upon higher-priority arrival). ECUs using **FIFO** TX queues or limited non-abortable mailbox sets suffer **priority inversion inside the local controller**, requiring the extended FIFO/mixed-queue analysis of Davis et al. (2011) rather than the pure priority-queue busy-period formula in Section 1.3.
- **Known not to apply — `can-utils` `canframelen.c` to Safety-Critical CAN-FD Timing Certification:** Direct source inspection and `Probe 2A-ii` prove that `canframelen.c:239-270` (`834ceef1f1eabec67625389172eebf1050d2f42b`) underestimates worst-case CAN-FD lengths by 4–9 bits, misclassifies 16-byte payloads as CRC-21, and returns `0` for `CFL_EXACT`; it must not be used as an oracle for CAN-FD WCRT.
- **Known not to apply — `AUTOSAR E2E` Against Active Bus Adversaries:** E2E CRCs and unkeyed counters offer zero cryptographic integrity against a compromised ECU on the bus, and neither E2E nor SecOC prevents physical/data-link TEC Bus-Off muting.
- **Known not to apply — Single-Core ARINC 653 Proofs to Unmitigated Multicore COTS SoCs:** Proving window schedulability in isolation does not carry over to concurrent multicore execution without explicit hardware interference channel mitigation (`AMC 20-193` / `AC 20-193`) as demonstrated in `Probe 2C`.
- **Unsupported — Cache/DRAM Isolation and Complete APEX Status in `pok-kernel/pok` x86:** At revision `b2e1cc382f86adba47cb93f015d92bc2d11cf40e`, `pok` provides neither cache coloring nor memory-bandwidth policing in `kernel/arch/x86/space.c`, and its `CLEAR_QUEUING_PORT` returns `NOT_AVAILABLE` (`libpok/arinc653/queueing.c:134-139`).
- **Not examined — CAN XL (`ISO 11898-1:2024`), Time-Sensitive Networking (IEEE 802.1Qbv), and FlexRay Static/Dynamic Segments:** Newer automotive backbones (CAN XL up to 2048 B with error-signaling disablement in fast mode, TSN credit-based / time-aware shapers) and formal verification of AUTOSAR SecOC freshness synchronization were outside this report's scope.
- **Not examined — Commercial Certified ARINC 653 RTOS Implementations (`VxWorks 653`, `PikeOS`, `Integrity-178 tuMP`):** Only the open-source `pok-kernel/pok` kernel source was directly inspected; commercial DAL-A hypervisors implement hardware-specific cache coloring, MPAM/CAT partitioning, and deterministic memory regulators not present in `pok`.
- **Unknown — Physical-Layer Clock-Drift Tolerance Bounds for Cho & Shin Synchronization Across Specific Transceiver Families:** While Cho & Shin (2016) demonstrated Bus-Off execution on commercial vehicles, exact minimum adversary clock-jitter margins across heterogeneous CAN-FD transceivers with Transceiver Delay Compensation (`TDC`) were not experimentally measured on physical hardware here.

## Evidence

### Primary Upstream Source Citations (Observed 2026-11-19)

1. **`linux-can/can-utils` @ `834ceef1f1eabec67625389172eebf1050d2f42b`:**
   - `canframelen.c:155-237` (`cfl_exact` exact Classical CAN CRC-15 `0x4599` + bit-stuffing simulator), `239-253` (`can_frame_dbitrate_length`), `255-283` (`can_frame_length`, including CAN-FD `frame->len >= 16` bug at line 263, `5/4` worst-case approximation at line 267, `CFL_EXACT` returning `0` at line 269, and Classical CAN `47+8*len` / `55+10*len` / `67+8*len` / `80+10*len` at lines 275-278).
   - `canbusload.c:131, 135-165` (`mode = CFL_WORSTCASE` default).
   - `include/linux/can/error.h:48-142` (`CAN_ERR_BUSOFF`, `CAN_ERR_CRTL_TX_PASSIVE`, `CAN_ERROR_WARNING_THRESHOLD = 96`, `CAN_ERROR_PASSIVE_THRESHOLD = 128`, `CAN_BUS_OFF_THRESHOLD = 256`).

2. **`torvalds/linux` @ `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`:**
   - `include/uapi/linux/can/error.h:130-141` (normative CAN error state thresholds).
   - `drivers/net/can/dev/dev.c:134-188` (`can_state_err_to_state`, `can_change_state`), `191-280` (`can_restart`, `can_restart_now`, `can_bus_off` invoking `netif_carrier_off` and optional `restart_ms` delayed work).

3. **`pok-kernel/pok` @ `b2e1cc382f86adba47cb93f015d92bc2d11cf40e`:**
   - `kernel/core/sched.c:96-123` (`pok_sched_init` MAF == sum-of-slots check), `137-186` (`pok_elect_partition` cyclic slot rotation and port-flush policies), `308-341` (`pok_global_sched` and `synchro_processors` SMP rendezvous).
   - `kernel/arch/x86/space.c:47-54` (`pok_space_switch`: GDT toggle only, no cache/DRAM isolation).
   - `kernel/middleware/portsamplingread.c:28-88` (lines 56-66: `pok_ports[pid].size` index bug + spinlock leak on `POK_ERRNO_EINVAL`; lines 77-81: `REFRESH_PERIOD` validity test).
   - `kernel/middleware/portsamplingwrite.c:39-76` (`pok_port_sampling_write` deferred flush flag).
   - `libpok/arinc653/sampling.c:24-123` and `libpok/arinc653/queueing.c:24-140` (APEX port API wrappers and `GET_QUEUING_PORT_STATUS` defect at lines 124-127).

### Primary Standards & Literature Citations

- `ISO 11898-1:2015`, *Road vehicles — Controller area network (CAN) — Part 1: Data link layer and physical signalling*.
- `ISO 26262:2018` (2nd ed.), *Road vehicles — Functional safety*, Parts 5 (Hardware), 6 (Software), and 9 (ASIL-oriented and safety-oriented analyses, Clauses 5 & 7).
- `AUTOSAR_PRS_E2EProtocol`, *Specification of E2E Protocol* (Profiles 1, 2, 4, 5, 6, 7, 11, 22).
- `ARINC Specification 653 Part 1`, *Avionics Application Software Standard Interface*.
- `EASA AMC 20-193` (2022) and `FAA AC 20-193` (2024), *Use of Multi-Core Processors* (formalizing `CAST-32A`).
- Robert I. Davis, Alan Burns, Reinder J. Bril, and Johan J. Lukkien, "Controller Area Network (CAN) schedulability analysis: Refuted, revisited and revised," *Real-Time Systems* 35(3):239–272, 2007, DOI `10.1007/s11241-007-9012-7`.
- Kyong-Tak Cho and Kang G. Shin, "Error Handling of In-vehicle Networks Makes Them Vulnerable," *ACM CCS 2016*, pp. 1044–1055, DOI `10.1145/2976749.2978360`.
- Heechul Yun, Gang Yao, Rodolfo Pellizzoni, Marco Caccamo, and Lui Sha, "MemGuard: Memory Bandwidth Reservation System for Efficient Performance Isolation in Multi-core Platforms," *IEEE RTAS 2013*, pp. 55–64.
- Jan Nowotsch, Michael Paulitsch, Daniel Bühler, Henrik Theiling, Simon Wegener, and Michael Schmidt, "Multi-core Interference-Sensitive WCET Analysis Leveraging Runtime Resource Capacity Enforcement," *ECRTS 2014*, pp. 109–118.

### Self-Contained Executable Micro-Probe (`Probes 2A, 2B, 2C, 2D`)

Executed with Python 3 (standard library only) on Linux x86_64 on `2026-11-19`:

```python
#!/usr/bin/env python3
"""Standalone micro-probes for Tindell vs Davis (2007) CAN WCRT, CAN-FD length,
Cho-Shin TEC Bus-Off state machine, ARINC 653 cache/DRAM interference, and ISO 26262 CCF."""
import math
from dataclasses import dataclass

@dataclass(frozen=True)
class Msg:
    name: str; prio: int; T: int; D: int; C: int

msgs = [Msg("m1", 1, 750, 750, 270), Msg("m2", 2, 750, 750, 270),
        Msg("mB", 3, 1150, 1150, 270), Msg("mL", 4, 20000, 20000, 190)]
tau = 2.0  # 500 kbit/s CAN 2.0A (2 us/bit)
m = msgs[2]; B = 190; hp = msgs[:2]; hep = msgs[:3]

# 2A: Tindell (q=0 only) vs Davis et al. (2007) exact busy-period WCRT
w = float(B)
while (wn := B + sum(math.ceil((w + tau) / j.T) * j.C for j in hp)) != w: w = wn
R_tindell = w + m.C
t = float(m.C)
while (tn := B + sum(math.ceil(t / j.T) * j.C for j in hep)) != t: t = tn
Q = math.ceil(t / m.T)
R_q = []
for q in range(Q):
    wq = float(B + q * m.C)
    while (wn := B + q * m.C + sum(math.ceil((wq + tau) / j.T) * j.C for j in hp)) != wq: wq = wn
    R_q.append((q, int(wq - q * m.T + m.C)))
print(f"2A Tindell R_B={int(R_tindell)} us (<=1150 PASS) | Davis t_B={int(t)}, Q={Q}, R_q={R_q} -> max={max(r for _, r in R_q)} us (FAIL!)")

# 2B: Cho & Shin TEC Bus-Off attack (Stage 1: Active->Passive; Stage 2: Passive->Bus-Off)
tv, ta, c = 0, 0, 0
while tv < 128: c += 1; tv += 8; ta += 8
c_ep = (c, tv, ta)
while tv < 256: c += 1; tv += 8; ta = max(0, ta - 1)
print(f"2B Error-Passive at collision #{c_ep[0]} (V={c_ep[1]},A={c_ep[2]}) | Bus-Off at #{c} (V={tv},A={ta})")

# 2C: ARINC 653 window (8.0 ms) vs unmitigated CRPD+DRAM vs cache-colored+MemGuard
print(f"2C Isolated=6.200 ms | Unmitigated={6.20 + 4096*120e-6 + 25000*110e-6:.3f} ms (OVERRUN) | Mitigated={6.20 + 25000*25e-6:.3f} ms")

# 2D: ISO 26262 ASIL B(D)+B(D) 1oo2 PMHF (lambda_ch=80 FIT, T_life=10,000 h)
lam, T_life = 80e-9, 10_000.0
for beta in (0.0, 0.05, 0.10, 0.15):
    pmhf = (beta * lam + ((1 - beta) ** 2) * (lam ** 2) * T_life) * 1e9
    print(f"2D beta={beta*100:4.1f}% -> PMHF={pmhf:5.2f} FIT ({'PASS' if pmhf < 10 else 'FAIL'})")
```

Observed output from the full 4-probe harness (including the discrete-event bus simulator confirming `R_B(1) = 1200 us` and exact ISO 11898-1:2015 CAN-FD DP):

```text
=== PROBE 2A: Tindell (1994/1995) Refutation vs Davis et al. (2007) ===
CAN 2.0A @ 500 kbit/s (tau_bit=2 us), U=0.9643, implicit deadlines D_B=T_B=1150 us:
  Tindell (1994/1995) q=0 only: w_B=730 us, R_B=1000 us <= D_B=1150 us -> FALSELY SCHEDULABLE!
  Davis et al. (2007) exact:    t_B=6670 us, Q_B=6, per-instance R_B(q)=[(0, 1000), (1, 1200), (2, 860), (3, 520), (4, 720), (5, 380)]
  Davis et al. max R_B = 1200 us > D_B=1150 us -> DEADLINE MISS on q=1!
  Discrete-event bus simulator: max R_B = 1200 us (observed on instance q=1) -> MATCHES DAVIS EXACTLY!

=== PROBE 2A-ii: ISO 11898-1:2015 CAN-FD vs linux-can/can-utils canframelen.c ===
D(B) | ISO_CRC | cu_CRC | ISO_unstuff | cu_unstuff | ISO_WC_exact | cu_WC(5/4) |  Delta
   0 |      17 |     17 |          62 |         46 |           66 |         57 |     -9
   8 |      17 |     17 |         126 |        110 |          146 |        137 |     -9
  12 |      17 |     17 |         158 |        142 |          186 |        177 |     -9
  16 |      17 |     21 |         190 |        178 |          226 |        222 |     -4
  20 |      21 |     21 |         227 |        210 |          271 |        262 |     -9
  32 |      21 |     21 |         323 |        306 |          391 |        382 |     -9
  64 |      21 |     21 |         579 |        562 |          711 |        702 |     -9

=== PROBE 2B: Cho & Shin (CCS 2016) Two-Phase CAN Bus-Off Attack ===
  Collision #12 (Stage 1): Victim TEC= 96 [ERROR_WARNING] | Adversary TEC= 96 [ERROR_WARNING]
  Collision #16 (Stage 1): Victim TEC=128 [ERROR_PASSIVE] | Adversary TEC=128 [ERROR_PASSIVE]
  Collision #17 (Stage 2): Victim TEC=136 [ERROR_PASSIVE] | Adversary TEC=127 [ERROR_WARNING]
  Collision #32 (Stage 2): Victim TEC=256 [BUS_OFF      ] | Adversary TEC=112 [ERROR_WARNING]
  Total collisions to mute victim ECU: 32 (~5.44 ms at 500 kbit/s; Adversary remains active at TEC=112)
  ISO 11898-1 Bus-Off recovery minimum idle time: 128 * 11 = 1408 recessive bits (2.816 ms at 500 kbit/s)

=== PROBE 2C: ARINC 653 Partition Window vs Shared Cache/DRAM Interference ===
  ARINC 653 Partition A window:     8.000 ms (MAF=20.0 ms)
  Isolated single-core WCET:        6.200 ms (margin +1.800 ms)
  Unmitigated multicore WCET:       9.442 ms (CRPD +0.492 ms, DRAM +2.750 ms) -> OVERRUN by 1.442 ms!
  Cache-colored + MemGuard WCET:    6.825 ms (margin +1.175 ms) -> SCHEDULABLE

=== PROBE 2D: ISO 26262 ASIL B(D)+B(D) Decomposition PMHF vs CCF Beta-Factor ===
  Per-channel lambda_ch = 80 FIT, T_life = 10000 h, Parent ASIL D limit = 10.0 FIT:
    beta=  0.0% -> CCF=  0.00 FIT, Indep=0.0640 FIT, Total PMHF=  0.06 FIT [PASS (<10 FIT)]
    beta=  1.0% -> CCF=  0.80 FIT, Indep=0.0627 FIT, Total PMHF=  0.86 FIT [PASS (<10 FIT)]
    beta=  5.0% -> CCF=  4.00 FIT, Indep=0.0578 FIT, Total PMHF=  4.06 FIT [PASS (<10 FIT)]
    beta= 10.0% -> CCF=  8.00 FIT, Indep=0.0518 FIT, Total PMHF=  8.05 FIT [PASS (<10 FIT)]
    beta= 15.0% -> CCF= 12.00 FIT, Indep=0.0462 FIT, Total PMHF= 12.05 FIT [FAIL (>=10 FIT)]
    beta= 20.0% -> CCF= 16.00 FIT, Indep=0.0410 FIT, Total PMHF= 16.04 FIT [FAIL (>=10 FIT)]
```

## Revalidation

1. **Check `linux-can/can-utils` CAN-FD frame length formulas:** Diff `canframelen.c` (`can_frame_length`, `can_frame_dbitrate_length`, lines 239-270) against revision `834ceef1f1eabec67625389172eebf1050d2f42b`. Verify whether `frame->len >= 16` has been fixed to `frame->len > 16`, whether `DLC`/`ESI`/Stuff-Count/Fixed-Stuff-Bits have been added, and whether `CFL_EXACT` is implemented for `CANFD_MTU`.
2. **Check `pok-kernel/pok` partition switching and sampling-port bugs:** Diff `kernel/arch/x86/space.c` (`pok_space_switch`), `kernel/middleware/portsamplingread.c:56-66` (`pok_ports[pid].size` and lock-release path), and `libpok/arinc653/queueing.c:117-132` against revision `b2e1cc382f86adba47cb93f015d92bc2d11cf40e`.
3. **Check Linux SocketCAN default Bus-Off recovery behavior:** Diff `drivers/net/can/dev/dev.c` (`can_bus_off`, `can_restart_now`, lines 241-280) against revision `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd` to verify whether `restart_ms` remains `0` (manual recovery) by default.
4. **Re-run inline verification probes:** Run the self-contained Python 3 probe from **Evidence** to re-confirm the Davis et al. (2007) busy-period counterexample (`1000 us` vs. `1200 us`), the ISO 11898-1:2015 32-collision TEC Bus-Off trajectory, the ARINC 653 multicore WCET overrun margin, and the ISO 26262 $\beta$-factor PMHF threshold. For any target vehicle or aircraft platform, substitute actual CAN IDs/payloads/bitrates, measured hardware cache/DRAM miss latencies, and certified component FIT rates into the same formulas.
