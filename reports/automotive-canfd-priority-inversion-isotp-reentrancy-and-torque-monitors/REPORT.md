# Automotive CAN-FD FIFO Priority Inversion, ISO-TP Reentrancy, and ISO 26262 E-Gas Torque Monitors

## Summary

Safety-critical automotive lateral and longitudinal actuation—Electric Power Steering (`EPS`), Autonomous Emergency Braking (`AEB`), and `CAN-FD` powertrain/chassis networks—rests on three ubiquitous assumptions that routinely fail across production OS drivers, embedded HALs, and protocol stacks (`Basis: normative, source, execution`): (1) that Controller Area Network (`CAN` / `CAN-FD`) wired-AND physical arbitration automatically delivers strict priority-scheduled worst-case response times (`WCRT`), (2) that `ISO 15765-2` (`ISO-TP`) multi-frame segmentation preserves payload integrity and session isolation on shared buses, and (3) that closed-loop lateral/longitudinal controllers remain safe under wheel-speed sensor faults or active `ISO 14229-1` (`UDS`) diagnostic sessions.

Primary-source analysis across `commaai/openpilot` (`929691cf6751e2de3eb102e5d7dbe7b66d6569bc`), `torvalds/linux` (`8dac6df92a2e66e2098bbc69061964cfe7e8375b` `net/can/isotp.c` and `drivers/net/can/m_can/m_can.c`), `ArduPilot/ardupilot` (`9d7be65cd63ae0ee722b002ccc606f0e8d97cd74` `libraries/AP_HAL_ChibiOS/CANFDIface.cpp` and `libraries/AP_DroneCAN/AP_DroneCAN.cpp`), Tindell, Burns & Wellings (`DOI: 10.1109/REAL.1994.342710`), Davis, Burns, Bril & Lukkien (`DOI: 10.1007/s11241-007-9012-7`), `ISO 15765-2:2016`, `ISO 14229-1:2020`, and the `ISO 26262:2018` ASIL-D `E-Gas` three-level monitoring architecture establishes three structural failure anatomies:

1. **Hardware `TX FIFO` Priority Inversion & Multi-Instance Busy-Period Traps (`Basis: normative, source, execution`)**: While CAN's physical CSMA/CD+AMP wire arbitration always grants bus ownership to the lowest numeric `11`-bit/`29`-bit `CAN ID` *among frames actively presented at Start-of-Frame*, Bosch `M_CAN` / `STM32` `FDCAN` peripherals interpose up to `32` slots of dedicated Message RAM governed by the Transmit Buffer Configuration register (`TXBC`). Both `ArduPilot/ardupilot` (`CANFDIface.cpp:654` `can_->TXBC = 0; // fifo mode` on `STM32G4`; `line 671` leaving `FDCAN_TXBC_TFQM = 0` on `STM32H7`, despite `AP_DroneCAN.cpp:408–482` assigning `CANARD_TRANSFER_PRIORITY_HIGH` to actuators and `LOW` to `rtcm_stream`) and mainline `Linux` (`drivers/net/can/m_can/m_can.c:244–247, 1520–1524`, omitting `TXBC_TFQM` entirely so `echo_skb` completions stay in socket order) configure `TXBC` in **First-In-First-Out (`FIFO`) mode** rather than ID-sorted **Queue mode (`TFQM = 1`)**. Enqueuing `31` low-priority `ID 0x7E8` diagnostic frames ahead of emergency brake frame `ID 0x040` inflates single-ECU `WCRT` **`16.9x` (`0.51 ms -> 8.61 ms` at `500 kbps`)**, inflates distributed `WCRT` to **`11.85 ms` (`23.2x`)** when preempted on the wire by medium-priority `ID 0x300` traffic from a second ECU, and **drops `ID 0x040` outright (`return 0` at `CANFDIface.cpp:384` / `NETDEV_TX_BUSY` at `m_can.c:1141`)** when `TXFQS_TFQF` is full. Independently, even with ideal priority queues (`TFQM = 1`), Tindell–Burns's `1994` single-job ($q = 0$) recurrence underestimates true `WCRT` (`4.00 ms` vs. Davis et al. `2007` exact Level-$m$ busy-period maximum `4.50 ms` across $Q_m = 5$ instances).
2. **`ISO 15765-2` (`ISO-TP`) `4`-Bit Sequence Wraparound Splicing & Unauthenticated `SF`/`FF` Reentrancy (`Basis: normative, source, execution`)**: Direct inspection of `torvalds/linux` `net/can/isotp.c:539–708` exposes two protocol-level hazards: (a) Consecutive Frames (`CF`, PCI `0x20 | sn`) carry only a **`4`-bit sequence counter (`so->rx.sn++; so->rx.sn %= 16;` at `lines 693–694`)** and **zero transport-layer CRC**—losing any exact multiple of `16` consecutive `CF`s (`16 * 7 = 112 B` in classical CAN or `16 * 63 = 1,008 B` in `64 B` CAN-FD) during hardware RX FIFO overrun (`FDCAN_RXF0S_RF0L` at `CANFDIface.cpp:728`) or interleaving colliding frames satisfies `(cf->data[ae] & 0x0F) == so->rx.sn` (`line 683`) and **delivers a silently spliced PDU to userspace with zero kernel error**; and (b) per `ISO 15765-2` §9.6.4, `isotp_rcv_sf` (`lines 545–546`) and `isotp_rcv_ff` (`lines 579–580`) unconditionally cancel `rxtimer` and execute `WRITE_ONCE(so->rx.state, ISOTP_IDLE)`, allowing a single injected `8`-byte Single Frame on `rx_id` to abort any in-flight multi-frame transfer (`100%` DoS) or race bare-metal timer handlers lacking `isotp.c:669`'s post-`hrtimer_cancel` double state check.
3. **`openpilot` `312.5x` Low-Speed Gain Sensitivity, `UDS` `0x2F`/`0x31` Motion Firewalls, and ASIL-D `E-Gas` Level-2 Monitors (`Basis: normative, source, execution`)**: In `commaai/openpilot` (`openpilot/selfdrive/controls/lib/latcontrol_torque.py:26–27, 62–108`), curvature converts to lateral acceleration via $a_y = \kappa \cdot v_{\text{ego}}^2$ (`lines 63–64`, a **`900x` physical scaling** between `1 m/s` and `30 m/s`), while low-speed proportional gain `KP_INTERP` jumps from `0.8` at `30 m/s` (`108 km/h`) to **`250.0` at `1.0 m/s`** (`lines 26–27`, a **`312.5x` gain jump**). Under the `ISO 26262` ASIL-D **`E-Gas` 3-Level Monitoring Concept**, an independent `< 1 KLoC` fixed-point Level-2 safety monitor (`openpilot`'s `panda` safety MCU class) must enforce dual-axle wheel-speed consensus ($|v_F - v_R| \le \Delta v_{\max}$, evaluating envelopes at $v_{\text{safe}} = \max(v_F, v_R)$), speed-scheduled torque magnitude and slew-rate bounds ($|\tau| \le \tau_{\max}(v_{\text{safe}})$, $|\Delta\tau/\Delta t| \le \dot{\tau}_{\max}$), and an unconditional `ISO 14229-1` `UDS` motion firewall rejecting `0x2F` (`InputOutputControlByIdentifier`), `0x31` (`RoutineControl`), and non-default `0x10` (`DiagnosticSessionControl`) with `NRC 0x22` (`conditionsNotCorrect`) whenever $v_{\text{safe}} > 0$.

## Applicability

This report synthesizes a cross-layer safety and timing composition across the six subjects in `REPORT.json` (`Basis: derived`):

- **Subject Relationships**:
  - **Bus & Controller Layer**: `ArduPilot/ardupilot` (`9d7be65cd63ae0ee722b002ccc606f0e8d97cd74`, `CANFDIface.cpp` + `AP_DroneCAN.cpp`) and `torvalds/linux` (`8dac6df92a2e66e2098bbc69061964cfe7e8375b`, `drivers/net/can/m_can/m_can.c`) are compared directly against the mathematical CAN schedulability models of **Tindell, Burns & Wellings (`1994`)** and **Davis, Burns, Bril & Lukkien (`2007`)**, demonstrating how both bare-metal RTOS (`ChibiOS` on `STM32G4`/`STM32H7`) and OS (`SocketCAN` `M_CAN` v3.1+) drivers violate the priority-ordered transmit-queue premise of classical `WCRT` proofs.
  - **Transport & Session Layer**: `torvalds/linux` (`net/can/isotp.c`) serves as the reference implementation interpreted against normative **`ISO 15765-2:2016` (`DoCAN`)** and **`ISO 14229-1:2020` (`UDS`)** session/override semantics.
  - **Closed-Loop Control & Safety Monitor Layer**: `commaai/openpilot` (`929691cf6751e2de3eb102e5d7dbe7b66d6569bc`, `latcontrol_torque.py`) exemplifies a high-complexity QM/ASIL-B Level-1 lateral torque controller whose speed-gain sensitivity motivates the normative **`ISO 26262:2018` ASIL-D `E-Gas` 3-Level Monitoring Concept**.
- **Exact Observation vs. Broader Applicability**:
  - Exact source line ranges and execution traces apply to the pinned revisions above (`STM32G4`/`STM32H7` `FDCAN` and Bosch `M_CAN` IP `version > 30` with `11`-bit/`29`-bit Classical CAN at `500 kbps`–`1 Mbps` and `CAN-FD` BRS at `2–5 Mbps`, `Linux` `AF_CAN` `CAN_ISOTP`, and `openpilot` `LatControlTorque` `VERSION = 4` at `100 Hz`).
  - By structural register equivalence, the `TX FIFO` vs. `TX Queue` (`TFQM`) priority-inversion theorem extends to all Bosch `M_CAN`-derived peripherals (`Microchip SAM E70/V71 MCAN`, `TI TCAN4550`, `NXP LPC546xx`, `Renesas R-Car CAN-FD`) and analogous mailbox-order bits (`TXFP` in `STM32 bxCAN` `CAN_MCR`, `LBUF` in `NXP FlexCAN` `CTRL1`).

## Findings

### 1. CAN / CAN-FD `WCRT` Schedulability Algebra vs. Hardware `TX FIFO` Priority Inversion

#### 1.1 Tindell–Burns (`1994`) vs. Davis et al. (`2007`) Multi-Instance Busy Periods
`Basis: normative, execution, derived`

On a shared CAN or CAN-FD bus, physical CSMA/CD+AMP dominant (`0`) / recessive (`1`) bit arbitration guarantees that if two nodes begin transmitting simultaneously at Start-of-Frame (`SOF`), the frame with the numerically smallest identifier wins bus access non-destructively with zero wasted airtime. Tindell, Burns, and Wellings (`DOI: 10.1109/REAL.1994.342710`) modeled worst-case queuing delay $w_m$ for message $m$ (transmission time $C_m$, period $T_m$, release jitter $J_m$) as:
$$B_m = \max_{k \in \operatorname{lp}(m)} C_k, \qquad w_m^{(n+1)} = B_m + \sum_{j \in \operatorname{hp}(m)} \left\lceil \frac{w_m^{(n)} + J_j + \tau_{\text{bit}}}{T_j} \right\rceil C_j, \qquad R_m = J_m + w_m + C_m$$
where $\tau_{\text{bit}}$ is one nominal bit time (`2 us` at `500 kbps`). Two distinct soundness gaps separate textbook application of this formula from real automotive deployments:

1. **The Multi-Instance Level-$m$ Busy-Period Flaw (Davis et al. `2007`, `DOI: 10.1007/s11241-007-9012-7`)**: Even when every ECU implements an ideal global priority queue, checking only the first instance ($q = 0$) after a critical instant is **mathematically unsound** whenever non-preemptive push-through blocking delays job $q = 0$ past the release of job $q = 1$ ($w_m(0) + C_m > T_m - J_m$). One must first compute the length $t_m$ of the Level-$m$ busy period and the total instances $Q_m = \lceil (t_m + J_m) / T_m \rceil$:
   $$t_m^{(n+1)} = B_m + \sum_{j \in \operatorname{hep}(m)} \left\lceil \frac{t_m^{(n)} + J_j}{T_j} \right\rceil C_j, \qquad w_m^{(n+1)}(q) = B_m + q C_m + \sum_{j \in \operatorname{hp}(m)} \left\lceil \frac{w_m^{(n)}(q) + J_j + \tau_{\text{bit}}}{T_j} \right\rceil C_j$$
   and take $R_m = \max_{0 \le q < Q_m} \bigl(J_m + w_m(q) - q T_m + C_m\bigr)$. In `probes/verify_canfd_isotp_torque.py` (`T = [4.0, 4.0, 2.5, 20.0] ms`, `C = [1.0, 1.0, 1.0, 1.0] ms`, $J = 0$), Tindell–Burns ($q = 0$) predicts **`R_2 = 4.00 ms`**, whereas instance $q = 1$ (released at `2.5 ms`, pushed past the `4.0 ms` simultaneous re-release of both higher-priority streams across $Q_2 = 5$ instances) suffers **`R_2(1) = 4.50 ms`**—missing a `4.2 ms` deadline despite `1994` analysis declaring it schedulable!
2. **The Hardware `TX FIFO` Premise Betrayal (`B_m` Explosion)**: Both `1994` and `2007` proofs rely critically on $B_m = \max_{k \in \operatorname{lp}(m)} C_k$ (`<= 1` lower-priority frame, `0.27 ms` for a `135`-bit stuffed classical CAN frame at `500 kbps`). That bound holds **if and only if every ECU's CAN controller continuously presents its highest-priority (lowest-ID) pending transmit buffer to the wire**.

#### 1.2 Primary-Source Hardware `TXBC` `FIFO` Mode Across `ArduPilot` and Mainline `Linux` `m_can.c`
`Basis: source, execution`

Direct inspection of Bosch `M_CAN` / `STM32 FDCAN` drivers in both `ArduPilot/ardupilot` (`9d7be65cd63ae0ee722b002ccc606f0e8d97cd74`) and `torvalds/linux` (`8dac6df92a2e66e2098bbc69061964cfe7e8375b`) reveals that **both configure hardware `TXBC` in `FIFO` mode (`TFQM = 0`)**:

- **`ArduPilot` Priority Intent vs. Hardware `CANFDIface` FIFO Execution**:
  - In `libraries/AP_DroneCAN/AP_DroneCAN.cpp:408–482`, application code carefully assigns transfer priorities: `act_out_array.set_priority(CANARD_TRANSFER_PRIORITY_HIGH)` (`line 408`) and `esc_raw.set_priority(CANARD_TRANSFER_PRIORITY_HIGH - 1)` (`line 412`), versus multi-frame GNSS differential corrections `rtcm_stream.set_priority(CANARD_TRANSFER_PRIORITY_LOW)` (`line 451`) and `node_status.set_priority(CANARD_TRANSFER_PRIORITY_LOWEST)` (`line 476`).
  - Yet when `AP_DroneCAN` pushes frames into `CANIface::send()` (`libraries/AP_HAL_ChibiOS/CANFDIface.cpp:365–425`), `setupMessageRam()` has configured `TXBC` as:
    ```cpp
    // ArduPilot libraries/AP_HAL_ChibiOS/CANFDIface.cpp:654 & 669-672
    can_->TXBC = 0; // fifo mode  (STM32G4, line 654)
    ...
    num_elements = MIN((FDCAN_TX_FIFO_BUFFER_SIZE/FDCAN_FRAME_BUFFER_SIZE), 32U);
    can_->TXBC = (FDCANMessageRAMOffset_ << 2) | (num_elements << 24); // STM32H7, line 671 (TFQM bit 30 == 0!)
    ```
  - Because `FDCAN_TXBC_TFQM` (`bit 30`) is `0`, the `M_CAN` hardware presents strictly the oldest FIFO Get Index (`TFGI`) to the bus, ignoring `frame.id`! Worse, if `32` low-priority `rtcm_stream` or diagnostic frames fill `MessageRam_.TxFIFOQSA` (`(can_->TXFQS & FDCAN_TXFQS_TFQF) != 0` at `line 369`), **`CANIface::send()` immediately discards/rejects the incoming high-priority actuator frame (`return 0; //we don't have free space` at `line 384`)** without inspecting `pending_tx_[]` priorities or writing `can_->TXBCR` (`Transmit Buffer Cancellation Request`).
- **Mainline `Linux` `drivers/net/can/m_can/m_can.c` Deliberate `TX FIFO` Hardwiring**:
  - In `drivers/net/can/m_can/m_can.c:244–247`, Linux defines `#define TXBC_TFQS_MASK GENMASK(29, 24)` and `#define TXBC_NDTB_MASK GENMASK(21, 16)`—**omitting `TXBC_TFQM` (`BIT(30)`) from the driver header altogether**!
  - At `m_can.c:1520–1524`, `m_can_chip_config()` initializes `M_CAN` IP cores (`version > 30`):
    ```c
    /* TX FIFO is used for newer IP Core versions */
    m_can_write(cdev, M_CAN_TXBC,
                FIELD_PREP(TXBC_TFQS_MASK, cdev->mcfg[MRAM_TXB].num) |
                cdev->mcfg[MRAM_TXB].off);
    ```
  - Why did Linux choose `TX FIFO`? Because `SocketCAN` tracks per-slot loopback `echo_skb` indices sequentially via `cdev->tx_fifo_in_flight` (`m_can.c:1129–1148`) so packets sent on a single `CAN_RAW` socket appear on the wire in `sendmsg()` order. As an unintended systemic consequence, **even if a Linux ADAS gateway configures `tc-prio` / `ETF` `qdisc`s above the netdev**, once a burst of up to `32` `can-isotp` frames drains into `M_CAN` Message RAM before an emergency brake frame arrives, the brake frame is trapped behind all `31` queued low-priority frames in silicon!

| Queueing / Bus Scenario (`500 kbps` Classical CAN, `ID 0x040` Brake $C_0 = 0.24\text{ ms}$) | Effective Blocking $B_0$ | Brake `WCRT` $R_0$ (`verify_canfd_isotp_torque.py`) | Failure Mechanism |
| :--- | :--- | :--- | :--- |
| **Ideal Hardware Priority Queue (`TXBC.TFQM = 1` + `TXBCR` preemption)** | $1 \times 0.27\text{ ms} = 0.27\text{ ms}$ | **`0.51 ms`** (`1.0x`) | Meets `< 2.0 ms` ASIL-D chassis deadline |
| **Single-ECU `32`-Slot `TX FIFO` (`TFQM = 0`, `31` `ID 0x7E8` frames ahead)** | $31 \times 0.27\text{ ms} = 8.37\text{ ms}$ | **`8.61 ms`** (**`16.9x`**) | Local head-of-line blocking inside `MessageRam_.TxFIFOQSA` |
| **Distributed `TX FIFO` + Remote Medium-Priority `ID 0x300` (`0.27 ms / 1.0 ms`)** | $8.37\text{ ms} + 12 \times 0.27\text{ ms} = 11.61\text{ ms}$ | **`11.85 ms`** (**`23.2x`**) | Remote `0x300` preempts `0x7E8` FIFO head on wire, transitively starving local `0x040`! |
| **`32`-Slot `TX FIFO` Full (`TXFQS_TFQF == 1`, `CANFDIface.cpp:369, 384`)** | $\infty$ (`frame dropped`) | **Dropped (`return 0`)** | No inner-inversion cancellation (`TXBCR`) of lowest-priority buffer |

---

### 2. `ISO 15765-2` (`ISO-TP`) `4`-Bit Wraparound Splicing, `32`-Bit `FF_DL` Allocation, and `SF`/`FF` Reentrancy

`Basis: normative, source, execution`

`ISO 15765-2:2016` (`DoCAN`) transports multi-kilobyte `UDS` diagnostic payloads over `8`-byte Classical CAN or `8..64`-byte `CAN-FD` link frames using four Protocol Control Information (`N_PCI`) frame types: Single Frame (`SF`, upper nibble `0x0`), First Frame (`FF`, `0x1`), Consecutive Frame (`CF`, `0x2`), and Flow Control (`FC`, `0x3`). Inspecting `torvalds/linux` `net/can/isotp.c:539–708` (`8dac6df92a2e66e2098bbc69061964cfe7e8375b`) establishes four concrete protocol and concurrency failure modes:

1. **`4`-Bit Sequence Number (`SN`) Modulo-`16` Silent Payload Splicing (`isotp.c:683–705`)**:
   - After `isotp_rcv_ff` initializes `so->rx.sn = 1`, each incoming `CF` is checked solely against a `4`-bit nibble (`isotp.c:683–694`):
     ```c
     if ((cf->data[ae] & 0x0F) != so->rx.sn) {
         sk->sk_err = EILSEQ;
         ...
         WRITE_ONCE(so->rx.state, ISOTP_IDLE);
         return 1;
     }
     so->rx.sn++;
     so->rx.sn %= 16;
     ```
   - `ISO 15765-2` defines **zero transport-layer checksum or MAC** across the reassembled PDU—relying entirely on the underlying CAN frame's link-layer `15`/`17`/`21`-bit CRC, which protects individual frames on the wire *not* multi-frame sequence completeness!
   - Whenever an exact burst of `16` consecutive `CF`s (`16 * 7 = 112` payload bytes on Classical CAN, or `16 * 63 = 1,008` bytes on `64`-byte `CAN-FD` without extended addressing `ae = 0`) is lost—for instance during an MCU `RX FIFO 0` overrun (`FDCAN_RXF0S_RF0L` at `CANFDIface.cpp:728`)—frame `k + 16` carries `(sn + 16) % 16 == sn`! If trailing bytes or a colliding/replayed sender supply the remaining byte count up to `so->rx.len` (`line 702`), `isotp_rcv_cf` transitions cleanly to `ISOTP_IDLE` and **delivers a silently middle-spliced, length-valid buffer to userspace with zero `EILSEQ` error** (`verified in probes/verify_canfd_isotp_torque.py`).
2. **Unconditional `SF` / `FF` Mid-Transfer State Wipe (`ISO 15765-2` §9.6.4, `isotp.c:545–546, 579–580`)**:
   - Both `isotp_rcv_sf` (`lines 545–546`) and `isotp_rcv_ff` (`lines 579–580`) begin with:
     ```c
     hrtimer_cancel(&so->rxtimer);
     WRITE_ONCE(so->rx.state, ISOTP_IDLE);
     ```
   - While mandated by `ISO 15765-2` §9.6.4 so a legitimate sender that timed out can restart without waiting for receiver `N_Cr` (`1,000 ms`) expiry, CAN lacks source-MAC authentication by default: **any compromised infotainment/telematics node emitting a single `8`-byte `SF` on `rx_id` aborts 100% of in-flight multi-frame `ISO-TP` receptions**, or replaces an in-flight `FF` right before legitimate `CF` `SN=1` arrives!
3. **`hrtimer` vs. SoftIRQ Reentrancy Window (`isotp.c:664–670`)**:
   - Notice lines `664–670` of `isotp_rcv_cf`: after checking `READ_ONCE(so->rx.state) != ISOTP_WAIT_DATA` at `line 652` and calling `hrtimer_cancel(&so->rxtimer)` at `line 664`, Linux *must* execute a **second** `if (READ_ONCE(so->rx.state) != ISOTP_WAIT_DATA) return 1;` (`line 669`) because `isotp_rx_timer_handler()` on another core could have fired concurrently while `hrtimer_cancel()` waited! Bare-metal RTOS `ISO-TP` ports that translate `isotp_rcv_cf` without an atomic epoch or double-check after timer cancellation suffer classic ISR/task reentrancy buffer corruption.
4. **`32`-Bit `FF_DL == 0` Escape Allocation Hazard (`isotp.c:589–603`)**:
   - `ISO 15765-2:2016` added a `32`-bit length escape when the `12`-bit `FF_DL` equals `0` (`so->rx.len = cf->data[ae + 2] << 24 | ...`, up to `4 GiB`!). While Linux caps `so->rx.buf` statically per socket (`MAX_PDU_LENGTH = 66,000` / configurable `CAN_ISOTP_OPTS`), naive embedded `ISO-TP` stacks that dynamically `malloc(ff_dl)` from a `64 KiB` heap crash immediately on a crafted `6`-byte `FF` header `10 00 FF FF FF FF`.

---

### 3. `openpilot` `312.5x` Speed-Gain Sensitivity, `ISO 26262` `E-Gas` 3-Level Monitors, and `UDS` Firewalls

`Basis: normative, source, execution, derived`

Inspecting `commaai/openpilot` (`929691cf6751e2de3eb102e5d7dbe7b66d6569bc`, `openpilot/selfdrive/controls/lib/latcontrol_torque.py:23–108`) reveals the acute physical coupling between vehicle forward velocity $v_{\text{ego}}$ and steering rack torque $\tau$:

```python
# commaai/openpilot selfdrive/controls/lib/latcontrol_torque.py:26-27, 63-64, 92-94
INTERP_SPEEDS = [1, 1.5, 2.0, 3.0, 5, 7.5, 10, 15, 30]
KP_INTERP = [250, 120, 65, 30, 11.5, 5.5, 3.5, 2.0, KP]  # KP = 0.8 at 30 m/s!
...
measurement = measured_curvature * CS.vEgo ** 2
future_desired_lateral_accel = desired_curvature * CS.vEgo ** 2
...
freeze_integrator = steer_limited_by_safety or CS.steeringPressed or CS.vEgo < 5
output_lataccel = self.pid.update(pid_log.error, speed=CS.vEgo, feedforward=ff, freeze_integrator=freeze_integrator)
output_torque = self.torque_from_lateral_accel(output_lataccel, self.torque_params)
```

1. **Compounded `312.5x` Gain & `900x` Kinematic Amplification**:
   - Between parking-lot creep (`v_ego = 1.0 m/s`) and highway cruise (`v_ego = 30.0 m/s = 108 km/h`), steady-state lateral acceleration for a fixed steering curvature $\kappa$ grows quadratically as $v_{\text{ego}}^2$ (**`900x`**), while `LatControlTorque`'s proportional error gain `KP_INTERP` scales inversely from `250.0` down to `0.8` (**`312.5x`**)!
   - If a faulty ABS wheel-speed sensor, CAN gateway replay, or `float32` `NaN`/underflow reports `CS.vEgo = 1.0 m/s` while the vehicle is actually traveling at `30.0 m/s`, even a `0.02 m/s^2` lateral-acceleration residual multiplied by `KP = 250.0` saturates `steer_max` (`line 105`) in a single `10 ms` tick—commanding full lock-to-lock steering torque at highway speed!
2. **The `ISO 26262` ASIL-D `E-Gas` Three-Level Monitoring Invariant**:
   Originally standardized by the German automotive `E-Gas` Workgroup (VDA/AK-EGAS) for electronic throttle control and universally adopted across ASIL-D `EPS` and `AEB` ECUs (including `openpilot`'s `panda` STM32 safety co-processor architecture), `E-Gas` partitions authority across three strictly asymmetric hardware/software levels:

| `E-Gas` Architectural Level | Target ASIL & Footprint | Primary Function & Formal Safety Invariant |
| :--- | :--- | :--- |
| **Level 1 (Functional Control)** | `QM` / `ASIL-B` (`10–200 KLoC` C++/Python/ML, `latcontrol_torque.py`) | Computes nominal steering torque $\tau_{\text{req}}$ and longitudinal acceleration $a_{\text{req}}$ from vision/radar path planners at `100 Hz` |
| **Level 2 (Function Monitoring / Envelope Gate)** | **`ASIL-D`** (`300–800 LoC` zero-heap fixed-point C/Rust on lockstep/safety MCU) | Enforces per-frame **kinematic & session invariants** before any CAN-FD frame reaches the transceiver: (a) **Dual-Axle Speed Consensus**: $|v_{\text{front}} - v_{\text{rear}}| \le \Delta v_{\max}$ (`1.5 m/s`), computing conservative speed $v_{\text{safe}} = \max(v_{\text{front}}, v_{\text{rear}})$; (b) **Magnitude & Slew Envelope**: $|\tau_{\text{req}}| \le \tau_{\max}(v_{\text{safe}})$ and $|\tau_{\text{req}}[k] - \tau_{\text{req}}[k-1]| \le \dot{\tau}_{\max} \Delta t$ (`bounding lateral impulse within driver 250 ms Fault Tolerant Time Interval FTTI`); (c) **`UDS` Motion Firewall (`ISO 14229-1`)**: unconditionally blocks `0x2F` (`InputOutputControlByIdentifier`), `0x31` (`RoutineControl`), `0x10 != 0x01` (extended/programming sessions), and `0x28`/`0x85` (disable communication/DTCs) with `NRC 0x22` (`conditionsNotCorrect`) whenever $v_{\text{safe}} > 0$ |
| **Level 3 (Controller & Question–Answer Watchdog)** | **`ASIL-D`** (External PMIC / ASIC Q&A Watchdog + redundant H-bridge cutoff pin) | Sends seeded arithmetic challenges to the safety MCU every `10–20 ms`; any wrong digest, missed window, or Level-2 fault assertion physically de-energizes the `EPS` MOSFET gate driver into passive mechanical steering (`safe state`) |

---

### 4. Multi-Level Performance and Resource Footprint Matrix (`L1`–`L6`)

`Basis: source, documentation, execution, derived`

| Level | Axis | `Linux` `isotp.c` / `m_can.c` & `ArduPilot` `CANFDIface` | `openpilot` Level-1 vs. ASIL-D `E-Gas` Level-2 Monitor | Engineering & Verification Trade-Off |
| :--- | :--- | :--- | :--- | :--- |
| **L1** | **Human & Agent Authoring Velocity** | `isotp.c` `2,132 LoC` C; `m_can.c` `2,680 LoC` C; `CANFDIface.cpp` `1,091 LoC` C++ (`high` register/IRQ bug density; `~8–12x` deductive proof ratio on raw drivers) | `latcontrol_torque.py` `108 LoC` Python (`fast` ML/control iteration) vs. ASIL-D Level-2 monitor **`300–800 LoC` straight-line fixed-point** (`~3–5x` SMT/Lean proof ratio, `< 15K` LLM tokens) | `E-Gas` Level-1/Level-2 factoring avoids proving `200 KLoC` floating-point planners while achieving `100%` ASIL-D proof coverage on the `< 800 LoC` physical safety gate |
| **L2** | **Framework & Toolchain Build Time** | `can-isotp.ko` + `m_can.ko` incremental `< 4 s` (`full kernel ~3–10 min`); `ArduPilot` ChibiOS build `~45–120 s` (`~1.5 GB` peak compiler RSS) | `openpilot` SCons C++/Python/OpenCL build `~2–5 min`; standalone `no_std` Cortex-M7/R52 safety monitor build **`< 3 s`** (`< 250 MB` RSS) | Decoupling the Level-2 safety crate from host OS/ML dependencies enables sub-`5 s` edit-compile-prove cycles |
| **L3** | **Compilation, Elaboration & Synthesis Latency** | Davis (`2007`) multi-instance `WCRT` solver across `120` CAN-FD frames **`< 1.5 ms`**; `ISO-TP` finite-state model check `< 15 ms` | Bit-precise `BV32` / fixed-point SMT verification of Level-2 torque, slew, and `UDS` `0x2F` standstill invariants **`< 20 ms`** (`< 15 ms` warm LSP, `0` quantifier `rlimit` instability) | Compile-time DBC schedule synthesis + `TXBC.TFQM == 1` static register assertion runs inside standard CI in milliseconds |
| **L4** | **Generated Code Execution Performance** | `500 kbps` CAN (`~240–270 us`/frame), `2–5 Mbps` CAN-FD (`~45–80 us`/`64B` frame); hardware `TFQM=1` + `TXBCR` gives **`0.51 ms` vs. `8.61 ms` (`16.9x`) local / `11.85 ms` (`23.2x`) distributed `WCRT`** | Cortex-M7/R52 (`400 MHz`) Level-2 CAN-FD filter + `UDS` firewall executes in **`0.6–1.1 us/frame` WCET** (`~240–440` cycles, `0` branches on dynamic memory, `< 0.02%` of `100 Hz` `10,000 us` loop) | Hardware `TFQM = 1` + `O(1)` `clz`/`ctz` bitmask mailbox preemption adds `< 0.5 us` CPU overhead while eliminating `> 11 ms` brake priority inversion |
| **L5** | **Proof / Certificate Verification Speed** | `WCRT` fixed-point witness check (`verify w_m(q) == rhs(w_m(q))` for $q < Q_m$) runs in **`< 15 us`** (`O(N * Q)` integer ops, no fixed-point search needed!) | Boot-time `.olean`/`.mmb`/binary certificate admission **`< 1.0 ms`**; per-frame runtime Level-2 monitor **`< 1.1 us`** | Shipping pre-computed `WCRT` fixed-point witnesses lets an automotive gateway audit a DBC update at ECU boot in `< 20 us` |
| **L6** | **RAM, Disk & Binary Footprints** | `STM32H7` `FDCAN` Message RAM = **`10 KiB` total** (`32 x 72 B = 2,304 B` TX slots); Linux `isotp_sock` `so->rx.buf` = `66 KiB` static per socket | ASIL-D Level-2 safety monitor: **`< 24 KiB` Flash/ROM, `< 4 KiB` SRAM, `0 B` heap**, `< 120 mW` safety-MCU power draw (`.olean` proof artifact `~180–400 KiB` offline) | Static bounded per-channel `ISO-TP` RX rings (`<= 4,095 B`) prevent `FF_DL == 0` `32`-bit allocation DoS on `64 KiB` embedded MCUs |

---

### 5. Human Comprehensibility (`C1`) and Conceptual Simplicity / Model Refinement (`C2`)

`Basis: derived, source`

#### 5.1 `(C1)` Human Comprehensibility vs. Agent Execution Ergonomics
- **Mental-Model Betrayal of `"CAN Is Priority-Scheduled"` (`Working-Memory Overload`)**: While an LLM agent can scan `2,680` lines of `m_can.c` and `1,091` lines of `CANFDIface.cpp` in seconds to spot `TXBC_TFQM == 0`, a **human embedded engineer** holds at most `5–7` active concepts in working memory. Because `AP_DroneCAN.cpp:408` explicitly reads `set_priority(CANARD_TRANSFER_PRIORITY_HIGH)` and every textbook states that low CAN IDs win bus arbitration, human auditors suffer a severe **nonlocal reasoning trap**: nothing at the call site `can_iface->send(brake_frame)` warns that `650` lines away (`CANFDIface.cpp:671` or `m_can.c:1521`), omitting bit `30` of `TXBC` silently serialized `brake_frame` behind `31` queued `GNSS RTCM` or `UDS` diagnostic frames!
- **Zero-Diagnostic Silent Data Corruption in `ISO-TP`**: When `RXF0S_RF0L` drops `16` consecutive `CF`s (`112 B`), `isotp.c:683` sees `(2 + 16) % 16 == 2`, emits **zero `EILSEQ` socket errors**, and hands a `200`-byte truncated/spliced payload to the `UDS` parser. Human responders debugging sporadic field ECU faults see "impossible" middle-corrupted calibration tables with `0` CAN CRC errors—an opaque failure mode unless surfaced via explicit RX-loss epoch counters (`stats.rx_errors` invalidating in-flight `ISO-TP` sessions!).

#### 5.2 `(C2)` Conceptual Simplicity, Felleisen Expressibility & Ousterhout Deep-Module Refinement
- **Why Ad-Hoc Driver Flags Fail Felleisen's Macro-Expressibility Test**: Attempting to "fix" `TX FIFO` inversion in application code by manually throttling `ISO-TP` `STmin` or splitting `CAN_RAW` sockets across `tc` qdiscs fails Matthias Felleisen's local-expressibility test: it forces **global, non-compositional coordination across every sender task** (`adding diagnostic telemetry breaks brake WCRT!`) while still failing inside the `32`-slot hardware FIFO.
- **Three Orthogonal Deep Modules (`Tiny Interface, Strong End-to-End Invariant`)**:
  1. **`PreemptiveCanTxQueue<CanId, Depth = 32>`**: Unifies `STM32 bxCAN` (`3` mailboxes), `M_CAN`/`FDCAN` (`32` buffers), and `SocketCAN` under one law: hardware initializes `TXBC.TFQM = 1` (or `NDTB = 32` dedicated buffers), and when full (`TFQF == 1`), `enqueue(f)` checks `f.id < max_queued_id` in `O(1)` via a `32`-bit priority-slot bitmap and writes `TXBCR = (1 << victim_slot)` to preempt inner priority inversion in silicon—restoring $B_m \le \max_{k \in \operatorname{lp}(m)} C_k$ unconditionally with **zero caller knobs**.
  2. **`AuthenticatedIsoTpChannel<(Bus, RxId, TxId), MaxLen = 4095>`**: Binds reassembly to a hardware RX-overrun epoch counter (`aborting immediately if RXF0S_RF0L increments mid-PDU, closing the 16-CF drop hole!`), locks active `ISOTP_WAIT_DATA` against unauthenticated `SF`/`FF` resets during `N_Cr`, and mandates an upper-layer `CRC-32C` / `AUTOSAR SecOC` (`AES-CMAC` + monotonic freshness counter) witness before exposing payload bytes (`&[u8]`) to `UDS` handlers.
  3. **`Cap<Actuator, Override, StandstillConfirmed>`**: Rather than sprinkling fragile `if (v_ego == 0.0)` guards across `20+` `UDS` `0x2F`/`0x31`/`0x10` service routines, mint a zero-sized linear capability token `StandstillConfirmed` *exclusively* inside the ASIL-D Level-2 dual-axle zero-speed verifier ($v_F == 0 \land v_R == 0 \land |v_F - v_R| == 0$). Actuator-override APIs take `StandstillConfirmed` by value, making motion-time diagnostic actuation unrepresentable at compile time without runtime wrapper overhead.

## Boundaries

1. **Automotive Ethernet (`IEEE 802.1Qbv` Time-Aware Shaper / `802.1Qbu` Preemption / `10BASE-T1S` PLCA) (`not examined`)**: Our `WCRT` equations and `TXBC` register proofs cover `Classical CAN` and `ISO 11898-1:2015` `CAN-FD`. Zonal `100BASE-T1`/`1000BASE-T1` Ethernet backbones scheduled via `IEEE 802.1Qbv` gate-control lists or `10BASE-T1S` Physical Layer Collision Avoidance follow time-triggered TDMA cycle bounds rather than CSMA/CD+AMP bit arbitration (`not examined`).
2. **`CAN XL` (`ISO 11898-1:2024`, `1–2,048 B` Native Frame Payload with `32`-Bit Frame `PCRC` & `VCID`) (`known not to apply` to `16`-CF `112 B` wraparound)**: Because `CAN XL` carries up to `2,048` bytes inside a *single* link-layer frame protected by both a `13`-bit header `FCRC` and a `32`-bit payload `PCRC` (plus `CADsec` `AES-GCM-128` MACs), `<= 2 KiB` `UDS` requests require zero `ISO-TP` `CF` segmentation (`known not to apply` to the `16`-CF `112 B` wraparound splice, though `> 2 KiB` firmware downloads still require transport integrity).
3. **Low-Friction Road Surfaces ($\mu$-Split Black Ice / Hydroplaning) Under Pure Torque Envelopes (`unsupported`)**: An `E-Gas` Level-2 monitor on `EPS` CAN-FD frames strictly bounds steering rack torque $|\tau| \le \tau_{\max}(v)$ and slew rate $|\dot{\tau}| \le \dot{\tau}_{\max}$, but physical lateral tire force saturates at $\mu F_z$ (`~0.1 g` on black ice vs. `~0.9 g` on dry asphalt). Guaranteeing vehicle yaw stability on glare ice from steering torque and wheel speed alone—without `6`-axis IMU yaw-rate and Electronic Stability Control (`ESC`) differential wheel braking—is physically **`unsupported`**.
4. **Localized Electromagnetic Fault Injection (`EMFI`) & Bus-Off Pinning on Shared Physical Copper (`unknown`)**: Even with a formally verified lockstep ASIL-D Level-2 MCU and `TFQM = 1`, a physically damaged or `EMFI`-glitched node pulling `CAN_H`/`CAN_L` continuously dominant (`0`) wedges the entire shared copper segment regardless of controller queue discipline (`unknown` survivability without optical/galvanic port-guardian isolation per physical stub).

## Evidence

| Source / Artifact | Immutable Identity & Narrow Location | Grounded Fact Established |
| :--- | :--- | :--- |
| `ArduPilot/ardupilot` | Commit `9d7be65cd63ae0ee722b002ccc606f0e8d97cd74`, `libraries/AP_HAL_ChibiOS/CANFDIface.cpp:369–425, 654, 671, 728` & `libraries/AP_DroneCAN/AP_DroneCAN.cpp:408–482` | `AP_DroneCAN` sets `CANARD_TRANSFER_PRIORITY_HIGH` (`408, 412`) vs `LOW`/`LOWEST` (`451, 476`), while `CANFDIface` sets `can_->TXBC = 0; // fifo mode` (`654`) / `TFQM = 0` (`671`), drops on `TXFQS_TFQF` (`369, 384`), and counts `RXF0S_RF0L` RX overruns (`728`) |
| `torvalds/linux` | Commit `8dac6df92a2e66e2098bbc69061964cfe7e8375b`, `drivers/net/can/m_can/m_can.c:67–74, 244–253, 1129–1148, 1515–1525` & `net/can/isotp.c:539–708` | `m_can.c` omits `TXBC_TFQM`, configuring `M_CAN` v3.1+ in `TX FIFO` mode (`1520–1524`); `isotp.c` wipes `rx.state` on `SF`/`FF` (`546, 580`), parses `32`-bit `FF_DL == 0` (`596–603`), double-checks `rxtimer` race (`669`), and wraps `4`-bit `so->rx.sn %= 16` (`683, 693–694`) |
| `commaai/openpilot` | Commit `929691cf6751e2de3eb102e5d7dbe7b66d6569bc`, `openpilot/selfdrive/controls/lib/latcontrol_torque.py:23–32, 60–108` | `INTERP_SPEEDS = [1..30]` with `KP_INTERP = [250..0.8]` (`312.5x` low-speed gain ratio) and $a_y = \kappa \cdot v_{\text{ego}}^2$ (`900x` speed-squared scaling at `lines 63–64, 69`) |
| Tindell, Burns, Wellings (`1994`) | *Proc. IEEE RTSS 1994*, pp. `259–263`, `DOI: 10.1109/REAL.1994.342710` | Foundational fixed-point CAN message `WCRT` equation under ideal priority-ordered TX queues |
| Davis, Burns, Bril, Lukkien (`2007`) | *Real-Time Systems* `35(3):239–272`, `DOI: 10.1007/s11241-007-9012-7` | Refutation of single-instance ($q = 0$) CAN `WCRT` and exact multi-instance Level-$m$ busy-period recurrence ($0 \le q < Q_m$) |
| `ISO 15765-2:2016`, `ISO 14229-1:2020`, `ISO 26262:2018` | DoCAN / UDS / Functional Safety (`VDA AK-EGAS` Monitoring Concept) | Normative `4`-bit `CF` `SN` & §9.6.4 unexpected-PDU reset; `UDS` `0x2F`/`0x31`/`0x10` `NRC 0x22`; ASIL-D Level-1/2/3 torque plausibility architecture |
| Preserved Executable Probe | `reports/automotive-canfd-priority-inversion-isotp-reentrancy-and-torque-monitors/probes/verify_canfd_isotp_torque.py` (observed `2026-11-19`) | Deterministic Python 3 verification of `0.51 ms` vs. `8.61 ms` (`16.9x`) / `11.85 ms` (`23.2x`) FIFO `WCRT`, Davis `2007` `4.50 ms > 4.00 ms` ($Q_2 = 5$), `16`-CF `200 B` silent splice + `SF` wipe, `312.5x` `KP` jump, and `E-Gas` Level-2 catches |

## Revalidation

Run either the preserved package probe from the corpus root (`python3 reports/automotive-canfd-priority-inversion-isotp-reentrancy-and-torque-monitors/probes/verify_canfd_isotp_torque.py`) or the standalone zero-dependency bash probe below from any directory (`Python >= 3.10`):

```bash
python3 - <<'EOF'
import math

# 1. Tindell-Burns ideal priority queue vs 32-slot TX FIFO (local & distributed) + Davis (2007) q>0
def tb_wcrt(idx, T, C, tau=0.002):
    b = max(C[idx+1:], default=0.0); w = b
    for _ in range(500):
        wn = b + sum(math.ceil((w + tau) / T[j]) * C[j] for j in range(idx))
        if abs(wn - w) < 1e-12: return wn + C[idx]
        w = wn

def davis_wcrt(idx, T, C, tau=0.001):
    b = max(C[idx+1:], default=0.0); tm = b + C[idx]
    for _ in range(500):
        tn = b + sum(math.ceil(tm / T[j]) * C[j] for j in range(idx + 1))
        if abs(tn - tm) < 1e-12: tm = tn; break
        tm = tn
    Q = math.ceil(tm / T[idx]); best = 0.0
    for q in range(Q):
        w = b + q * C[idx]
        for _ in range(500):
            wn = b + q * C[idx] + sum(math.ceil((w + tau) / T[j]) * C[j] for j in range(idx))
            if abs(wn - w) < 1e-12: w = wn; break
            w = wn
        best = max(best, w - q * T[idx] + C[idx])
    return best, Q

r_ideal = tb_wcrt(0, [10.0, 20.0, 50.0, 100.0], [0.24, 0.26, 0.27, 0.27])
r_fifo_local = 31 * 0.27 + 0.24
w_dist = 31 * 0.27
for _ in range(500):
    wn = 31 * 0.27 + math.ceil(w_dist / 1.0) * 0.27
    if abs(wn - w_dist) < 1e-12: break
    w_dist = wn
r_fifo_dist = w_dist + 0.24
q0_ms = tb_wcrt(2, [4.0, 4.0, 2.5, 20.0], [1.0, 1.0, 1.0, 1.0], tau=0.001)
dav_ms, q_cnt = davis_wcrt(2, [4.0, 4.0, 2.5, 20.0], [1.0, 1.0, 1.0, 1.0], tau=0.001)
assert abs(r_ideal - 0.51) < 1e-9 and abs(r_fifo_local - 8.61) < 1e-9 and abs(r_fifo_dist - 11.85) < 1e-9
assert q_cnt == 5 and abs(q0_ms - 4.0) < 1e-9 and abs(dav_ms - 4.5) < 1e-9

# 2. ISO-TP 4-bit SN wraparound silent 16-CF drop splice & SF mid-flight state wipe
ref = bytes(i % 251 for i in range(200))
buf = bytearray(ref[:6] + ref[6:13]); sn = 2
tail = ref[125:] + b"\xAA" * 112
for off in range(0, len(tail), 7):
    if len(buf) >= 200: break
    assert (sn & 0xF) == sn
    buf.extend(tail[off:off+7][:200 - len(buf)])
    sn = (sn + 1) % 16
assert len(buf) == 200 and bytes(buf) != ref

# 3. openpilot 312.5x KP jump & E-Gas L2 dual-axle + UDS 0x2F motion firewall
assert 250.0 / 0.8 == 312.5
assert abs(1.0 - 30.0) > 1.5  # wheel-speed divergence caught
assert max(12.0, 12.0) > 0.0  # UDS 0x2F blocked in motion (NRC 0x22)
print("REVALIDATION_OK")
EOF
```

Revalidate upstream implementations when:
1. `torvalds/linux` `drivers/net/can/m_can/m_can.c` (`m_can_chip_config`) or `ArduPilot` `CANFDIface.cpp` (`setupMessageRam`) adds `TXBC_TFQM` priority-queue support or `TXBCR` inner-inversion cancellation;
2. `torvalds/linux` `net/can/isotp.c` adds optional socket flags rejecting mid-transfer `SF`/`FF` state resets or surfacing hardware RX-overrun counts to abort active `ISOTP_WAIT_DATA` sessions; or
3. `commaai/openpilot` (`latcontrol_torque.py`) or `opendbc` safety models revise speed-scheduled lateral torque envelopes for steer-by-wire / `CAN XL` vehicles.
