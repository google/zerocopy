# Maritime COLREGs Velocity-Obstacle Chattering, Unauthenticated VHF AIS Spoofing, Shallow-Water Bank Suction, and Switchboard Undervoltage Blackouts

## Summary

Autonomous Unmanned Surface Vehicles (`USV`s), integrated bridge systems, and commercial ships transiting confined harbors and canals couple four distinct cyber-physical hazard surfaces—navigation rule state machines, unauthenticated RF telemetry, shallow-water hull-bank hydrodynamics, and shipboard electrical protection—whose uncoordinated interactions produce collisions, channel groundings, or total loss of propulsion and steering:

1. **IMO COLREGs Rules 13–17 Sector Chattering and Broken `inextremis` Latching**: Partitioning encounter geometry into discrete `Head-On` (Rule 14), `Crossing Give-Way` (Rules 15/16), `Crossing Stand-On` (Rule 17), and `Overtaking` (Rule 13) modes without dwell-locked maneuver commitment and past-CPA release gating causes `64` helm-mode reversals in `60 s` under `±1.8 deg` sea-state yaw perturbation (`Basis: execution`). Furthermore, direct source inspection of `MOOS-IvP`'s latest `BHV_AvdColregsV26::checkModeStandOn()` (`BHV_AvdColregsV26.cpp:925-975`) reveals a live latch-erasure bug: line `955` unconditionally assigns `m_avoid_submode = "unsure"` *before* line `964` tests `if(m_avoid_submode == "inextremis") return;`, rendering line `964` dead code and causing an emergency Rule 17(a)(ii)/17(b) `inextremis` evasive maneuver to revert to course-locked `standon:unsure` the instant predicted CPA nudges `0.2 m` above `m_min_util_cpa_dist` (`Basis: source + execution`).
2. **Unauthenticated VHF AIS Table-Eviction and Obstacle Injection**: Because ITU-R M.1371-5 VHF `AIS` frames carry no cryptographic authentication, `ArduPilot`'s `AP_AIS::get_vessel_index` (`libraries/AP_AIS/AP_AIS.cpp:383-458`, default `LIST_MAX = 25`) evicts the furthest tracked vessel whenever a newly received `!AIVDM` target reports a closer GPS coordinate (`dist < max_dist`), while `send_to_object_avoidance_database` (`AP_AIS.cpp:279-348`) injects every uncorroborated AIS report directly into `AP_OADatabase` with forged vessel radii up to `511 m`. A `0.94 s` RF burst of `25` spoofed Class A reports at `20`–`44 m` deterministically blinds `AP_AIS` to `100%` of real vessels beyond `45 m` while steering `AP_OABendyRuler` toward physical hazards (`Basis: source + execution`). Similarly, `OpenCPN` (`ais_decoder.cpp:4054-4064`) dead-reckons stale AIS targets forward along their last reported `SOG`/`COG` (`ll_gc_ll`) without an upper staleness clamp prior to target-lost expiry (`Basis: source`).
3. **Shallow-Water Squat and Asymmetric Bank-Suction Control-Authority Collapse**: In restricted waterways (*Ever Given*, Suez Canal, `2021-03-23`), hull sinkage (`squat`) scales as $V_k^{2.08}$ while Bernoulli low-pressure **bank suction** at the stern and high-pressure **bow cushion** generate a destabilizing bow-away yaw moment $N_{\text{bank}} \propto U^2 y_{\text{off}} (T / \text{UKC}_{\text{rem}})^{1.60}$. Accelerating a `400 m` ULCV from `8.0 kn` (`18 m` corridor) to `13.5 kn` (`45 m` off-centerline, e.g., lured by a phantom AIS target or crosswind drift) triples bow squat (`0.828 m -> 2.460 m`, shrinking under-keel clearance to `5.840 m`) and inflates $N_{\text{bank}}$ (`91.60 -> 967.14 MN·m`) past maximum `35 deg` rudder restoring authority (`758.82 MN·m`, net deficit `-208.31 MN·m`), making grounding hydrodynamically inevitable regardless of subsequent helm orders (`Basis: normative + derived + execution`).
4. **Fail-Open Switchboard Undervoltage Releases (`UVR`) and Non-Auto-Restarting Auxiliary Fuel Pumps**: Per NTSB Marine Investigation Report **`MIR-25-40` (`DCA24MM031`)** on the containership *MV Dali*'s `2024-03-26` allision with the Francis Scott Key Bridge, an instantaneous (`0 ms` delay) `110V DC` undervoltage-release (`UVR`) coil on high-voltage feeder breaker `HR1` (`6.6 kV -> TR1 -> 440 V` `LR1`), combined with a plastic wire-label sleeve preventing spring-clamp terminal insertion, `Manual` standby transformer (`TR2`) failover, and feeding online diesel generators (`DG3`, `DG4`) via a maintenance **fuel-oil flushing pump** lacking automatic restart after blackout, converted a transient wire-contact bounce into a **`58 s` first blackout** (tripping the main propulsion engine on cooling-water loss) followed `~2 min` later by a **second fuel-starvation blackout** `~320 m` from Pier 17 (`Basis: normative + execution`).

---

## Applicability

This report applies to autonomous surface vessel (`USV`) motion planners, Electronic Chart Display and Information Systems (`ECDIS` / chartplotters), marine sensor-fusion pipelines (`AIS` + `ARPA` marine radar + `GNSS`/`INS`), confined-channel pilotage envelope monitors, and shipboard high/low-voltage power management systems (`PMS`) across three pinned upstream codebases and five primary maritime specifications and casualty investigations:

- **`moos-ivp/moos-ivp` (`ab1ac374a44a5c567187b4f27abce2e02e8fbefa`)**: Multi-objective Interval Programming (`IvP`) helm (`pHelmIvP`) and the `lib_behaviors-colregs` library (`BHV_AvdColregsV17`, `V19`, `V22`, and `V26`, plus `AOF_R13`, `AOF_R14`, `AOF_R16`, `AOF_R17`, `AOF_CPA` under `ivp/src/lib_behaviors-colregs/`). Note how `MOOS-IvP` retains four coexisting historical versions (`V17`..`V26`) in one build target; section 1 below documents exact `V26` behavior (`1,796` lines) alongside shared `AOF` objective evaluators.
- **`OpenCPN/OpenCPN` (`cdc797ca09640b9af9b228d7545c1930437a7065`)**: NMEA 0183 / SignalK AIS decoding (`model/src/ais_decoder.cpp`, `model/src/ais_target_data.cpp`, `model/include/model/ais_target_data.h`), specifically commit `cdc797ca09640b9af9b228d7545c1930437a7065` (`#5557`), which introduced great-circle forward projection (`Lat_projected`, `Lon_projected`) inside `AisDecoder::UpdateOneCPA`.
- **`ArduPilot/ardupilot` (`9d7be65cd63ae0ee722b002ccc606f0e8d97cd74`)**: `AP_AIS` NMEA `!AIVDM` parser and vessel table (`libraries/AP_AIS/AP_AIS.cpp`), `AP_OADatabase` dynamic obstacle injection, `AP_OABendyRuler` bearing-hysteresis obstacle avoidance (`libraries/AC_Avoidance/AP_OABendyRuler.cpp`), and `Rover` `1 kHz` watchdog/battery failsafes (`Rover/failsafe.cpp`).
- **Normative Rules, Security Research & Official Casualty Reports**: IMO `1972 COLREGs` (Rules 8, 13–18), Kuwata et al. (`DOI 10.1109/JOE.2013.2254214`), Balduzzi, Pasta & Wilhoit (`DOI 10.1145/2664243.2664257`), NTSB `MIR-25-40` (`DCA24MM031`, *MV Dali*), and Panama Maritime Authority *MV Ever Given* Suez Canal Grounding Investigation (`2021-03-23`).

---

## Findings

### 1. IMO COLREGs Velocity Obstacles, Self-Induced Bearing Chattering, and the `BHV_AvdColregsV26` `inextremis` Bug

`Basis: normative + source + execution`

Given ownship position $\mathbf{p}_o$, velocity $\mathbf{v}_o = (U_o \sin\psi_o, U_o \cos\psi_o)$, and target vessel $i$ at $(\mathbf{p}_i, \mathbf{v}_i)$ with combined safety radius $R_{\text{safe}}$, the linear **Velocity Obstacle (`VO`)** cone is:
$$\mathcal{VO}_{o|i}(\tau_{\text{hor}}) = \left\{ \mathbf{v}_o \in \mathbb{R}^2 \;\middle|\; \exists t \in (0, \tau_{\text{hor}}]: \|(\mathbf{p}_o - \mathbf{p}_i) + (\mathbf{v}_o - \mathbf{v}_i) t\|_2 \le R_{\text{safe}} \right\}$$
Unlike symmetric robotics `ORCA`, IMO `COLREGs` breaks symmetry via relative bearing $\beta_{o \to i} = \operatorname{wrap}_{[0,360)}(\theta_{o \to i} - \psi_o)$ and contact aspect $\alpha_{i \to o} = \operatorname{wrap}_{[0,360)}(\theta_{i \to o} - \psi_i)$ (`Kuwata et al. 2014`, `BHV_AvdColregsV26.cpp`):
- **Rule 13 (Overtaking)**: Coming up abaft the other's beam (`> 22.5 deg` abaft beam, i.e., $\alpha_{i \to o} \in [112.5^\circ, 247.5^\circ]$, parameterized by `m_overtaking_bng_range = 67.5` around `180 deg` at `BHV_AvdColregsV26.cpp:70,585-586`). Under Rule 13(d), no subsequent bearing change relieves the overtaking vessel of keeping clear *until finally past and clear*.
- **Rule 14 (Head-On)**: Reciprocal or nearly reciprocal courses ($\min(\beta_{o \to i}, 360^\circ - \beta_{o \to i}) \le \beta_{\text{ho}}$ and $\min(\alpha_{i \to o}, 360^\circ - \alpha_{i \to o}) \le \beta_{\text{ho}}$, `m_headon_abs_relbng_thresh = 12.0` deg at `BHV_AvdColregsV26.cpp:74,710-711`); **both** vessels alter course to starboard (port-to-port passing; `AOF_R14.cpp:101-108` penalizes crossing the contact's bow when port-of-contact).
- **Rules 15 & 16 (Crossing Give-Way)**: Contact on ownship's starboard bow ($\beta_{o \to i} \in (12^\circ, 112.5^\circ]$, $\alpha_{i \to o} \ge 247.5^\circ$, `BHV_AvdColregsV26.cpp:799`); ownship takes early, substantial action (`Rule 8(b)`), avoiding crossing ahead (`Rule 15`, `m_avoid_submode = "stern"` default at `L810`).
- **Rule 17 (Crossing Stand-On)**: Contact on ownship's port bow ($\beta_{o \to i} \in [247.5^\circ, 348^\circ)$, $\alpha_{i \to o} \le 112.5^\circ$, `L942`); ownship **must hold course and speed** (`Rule 17(a)(i)`) unless it becomes apparent the give-way vessel is not taking appropriate action (`Rule 17(a)(ii)`, avoiding port turns per `Rule 17(c)`) or collision cannot be avoided by the give-way vessel alone (`Rule 17(b)` *in extremis*).

Two severe algorithmic pathologies emerge across boundary implementations:

1. **Wave-Yaw & Self-Induced Turn Chattering on the `Rule 14 / Rule 17` Seam**:
   Suppose a contact approaches at $\beta_{o \to i} = 11.8^\circ$ off starboard/port bow under `±1.8 deg` sea-state yaw oscillation. A memoryless sector classifier—or even a naive angular hysteresis band `[12 deg, 17 deg]` keyed on *current* relative bearing $\beta_{o \to i}(t)$—suffers **self-induced chattering**: entering `Rule 14` commands a `+24 deg` starboard turn (`\psi_o: 0 -> +24 deg`), which *immediately* drives $\beta_{o \to i}(t) = |\theta_{o \to i} - \psi_o(t)| > 17^\circ$ while the two vessels are still closing (`dR/dt < 0`), flipping ownship into `Stand-On` (`0 deg`) or releasing avoidance straight back across the contact's bow! As verified in `maritime_colregs_ais_dali_probe.py`, memoryless classification chatters **`64` times in `60 s`** (`CPA = 390.23 m`), whereas **past-CPA kinematic commitment** (releasing `Head-On` only when $\dot{R} = \frac{(\mathbf{p}_i - \mathbf{p}_o)\cdot(\mathbf{v}_i - \mathbf{v}_o)}{\|\mathbf{p}_i - \mathbf{p}_o\|} > 0$ after dwell $\tau_{\text{dwell}} = 15\text{ s}$, matching `BHV_AvdColregsV26.cpp:665`'s `rate_of_closure() < 0` check) produces **`1` clean transition** (`CPA = 426.34 m`). Compare `ArduPilot`'s `AP_OABendyRuler::resist_bearing_change` (`AP_OABendyRuler.cpp:381-417`), which suppresses bearing flips exceeding `_bendy_angle` unless candidate obstacle margin exceeds `_bendy_ratio * previous_bearing_margin` (`L400`), preventing geometric left/right oscillation around symmetric obstacles but remaining completely COLREGs-agnostic (`Rule 14` port turns vs. starboard turns carry identical Euclidean margin!).

2. **Live `inextremis` Submode Wipe Bug in `MOOS-IvP` `BHV_AvdColregsV26::checkModeStandOn()` (`Basis: source + execution`)**:
   In `ivp/src/lib_behaviors-colregs/BHV_AvdColregsV26.cpp:925-989`, `checkModeStandOn()` differs fatally from `checkModeOvertaking` (`L574`), `checkModeHeadOn` (`L688`), and `checkModeGiveWay` (`L791`), each of which executes `return;` at the end of Part 2 (`if(m_avoid_mode == "...")`):
   ```cpp
   // BHV_AvdColregsV26.cpp L925-975 (exact upstream source @ ab1ac374a44a5c567187b4f27abce2e02e8fbefa)
   if(m_avoid_mode == "standon") {
     if(m_cn_crossed_os_port_star) { resetAvoidModes(); return; }
     if((m_contact_range > m_min_util_cpa_dist) && (m_cnos.rate_of_closure() < 0)) {
       resetAvoidModes(); return;
     }
   } // <-- MISSING return; falls through into Part 3 entry assignment every tick!
   if((m_cnos.os_cn_rel_bng() < 247.5) || (m_cnos.cn_os_rel_bng() > 112.5)) return;
   if(!m_cnos.cn_crosses_os_bow_or_stern()) return;
   if(m_cnos.rate_of_closure() < 0) return;

   m_avoid_mode = "standon";
   m_avoid_submode = "unsure"; // <-- L955: UNCONDITIONALLY OVERWRITES m_avoid_submode!

   // kw added for rule 17.a.ii to allow in-extremis actions
   // once in extremis, retain authority to maneuver as necessary
   if(m_avoid_submode == "inextremis") // <-- L964: ALWAYS FALSE (DEAD CODE)!
     return;
   if((m_avoid_mode == "standon") && (m_contact_range <= m_max_util_cpa_dist) &&
      (m_cnos.os_curr_cpa_dist() <= m_min_util_cpa_dist)){
     m_avoid_submode = "inextremis";
     return;
   }
   ```
   Because line `955` overwrites `m_avoid_submode = "unsure"` *before* line `964`, the intended monotone latch (`"once in extremis, retain authority to maneuver as necessary"`) is **broken on 100% of helm iterations**: on tick $k$ (`CPA = 24.5 m <= 25.0 m`), ownship enters `standon:inextremis` and initiates an emergency starboard avoidance turn; on tick $k+1$, as soon as that turn nudges instantaneous projected CPA to `25.2 m` (`> 25.0 m`), `checkModeStandOn()` resets `m_avoid_submode` to `"unsure"`, snapping `pHelmIvP` back to `AOF_R17` course-and-speed hold (`m_osh_orig_standon`, `L500`) and steering ownship straight back into the rogue give-way vessel!

---

### 2. Unauthenticated VHF AIS Spoofing, `AP_AIS` Table Eviction, and Confined-Channel Bank Suction

`Basis: normative + source + derived + execution`

1. **Protocol-Level Zero Authentication & Upstream Parser Trust (`Balduzzi et al. 2014`, `ArduPilot`, `OpenCPN`)**:
   ITU-R M.1371-5 VHF `AIS` (`161.975 MHz` AIS1 / `162.025 MHz` AIS2, `9,600 bps` GMSK SOTDMA, `2,250` slots/min/channel = `26.67 ms`/slot) transmits `6`-bit ASCII armored payloads inside NMEA 0183 `!AIVDM` sentences guarded only by an `8`-bit XOR checksum (`*hh`) and `16`-bit HDLC FCS on air—**zero sender authentication, zero replay sequence counters, and zero RF range/bearing binding**.
   - **Nearest-Target Table Eviction & `511 m` Obstacle Injection in `ArduPilot` (`AP_AIS.cpp:279-458`)**: `AP_AIS` caps its vessel table at `_max_list = 25` (`AP_AIS.cpp:53`). When full, `AP_AIS::get_vessel_index` (`L433-457`) computes `max_dist` across `_list[0..24]` and **evicts the furthest vessel whenever a new MMSI claims `dist < max_dist`**. Simultaneously, `send_to_object_avoidance_database` (`L279-348`) converts Message 5 bow/stern/port/starboard fields (`9` bits each for bow/stern = `0..511 m`) into an `AP_OADatabase` circular obstacle of radius `MAX((bow + stern)*0.5, (stbd + port)*0.5)` up to **`511 m` (`1,022 m` diameter)** (`L342-347`). An inexpensive SDR (`$300` USRP/HackRF, Balduzzi et al. `ACSAC 2014`) transmitting `25` spoofed `Message 1` frames (`< 1 s` airtime) at virtual distances `20`–`44 m` from a `USV` deterministically **evicts `100%` of real vessels at `>= 45 m`** (`ap_ais_real_tanker_retained_after_25_spoofs == false`) while building a virtual funnel of `511 m` obstacles that herds `AP_OABendyRuler` laterally into canal banks or bridge piers.
   - **Unbounded Dead-Reckoning Extrapolation in `OpenCPN` (`ais_decoder.cpp:4045-4064`)**: At commit `cdc797ca09640b9af9b228d7545c1930437a7065`, `AisDecoder::UpdateOneCPA` computes `report_age = now.GetTicks() - ptarget->PositionReportTicks` (`L4058`) and projects `Lat_projected, Lon_projected` along `ptarget->COG` by `ptarget->SOG * (report_age / 3600.0)` (`ll_gc_ll`, `L4060-4062`) without capping `report_age` prior to target removal (`AIS_NoUpdate_Seconds`), allowing a single forged `100-knot` AIS burst (`SOG = 102.1 < 102.2`, `L4055`) to sweep a ghost CPA collision vector across miles of chart display for minutes after transmission stops.

2. **Shallow-Water Squat & Bank-Suction Yaw Sheer Envelope (*Ever Given*, Suez Canal `2021-03-23`)**:
   In a restricted canal of depth $h$, width $W$, and blockage ratio $S = (B \cdot T)/(W \cdot h)$, hull acceleration between the hull bottom/sides and channel boundaries causes:
   - **Barrass Shallow-Water Squat**: $S_{\max} \approx \frac{C_B \, S^{0.81} \, V_k^{2.08}}{20}\text{ (m)}$, reducing effective under-keel clearance to $\text{UKC}_{\text{rem}}(V_k) = (h - T) - S_{\max}(V_k)$.
   - **Norrbin / Lataire Asymmetric Bank-Suction & Bow-Cushion Yaw Moment**: When displaced laterally by $y_{\text{off}}$ toward a bank (`y_rel = y_off / [0.5(W - B)]`), Venturi flow acceleration along the near-bank quarter pulls the stern toward the bank while stagnation pressure pushes the bow toward the opposite bank, producing destabilizing yaw moment $N_{\text{bank}} = \frac{1}{2}\rho L^2 T U^2 c_{N,\text{bank}} \, y_{\text{rel}} \left(\frac{T}{\text{UKC}_{\text{rem}}(U)}\right)^{\!1.60}$, opposed by maximum rudder restoring moment $N_{\delta,\max} = \frac{1}{2}\rho A_R (U^2 + u_{\text{prop},0}^2) C_{L,\max} |x_R| \cos\delta_{\max}$.
   - Crucially, because $\text{UKC}_{\text{rem}}(U)$ **shrinks as $U^{2.08}$**, $N_{\text{bank}}(U)$ grows **super-quadratically** ($\sim U^{3.1}$–$U^{3.8}$) whereas rudder authority grows only **quadratically** ($\sim U^2$). For an *Ever Given*-class ULCV ($L = 400\text{ m}, B = 58.8\text{ m}, T = 15.7\text{ m}, C_B = 0.85$ in $h = 24.0\text{ m}, W = 205\text{ m}$, $S = 0.1876$):
     - At statutory **`8.0 kn`** ($F_{nh} = 0.268$, $y_{\text{off}} = 18\text{ m}$): squat is `0.828 m` ($\text{UKC}_{\text{rem}} = 7.472\text{ m}$) and $N_{\delta,\max} = 352.69\text{ MN}\cdot\text{m} \gg N_{\text{bank}} = 91.60\text{ MN}\cdot\text{m}$ (**`+261.09 MN·m` controllable margin**).
     - At recorded overspeed **`13.5 kn`** ($F_{nh} = 0.453$, $y_{\text{off}} = 45\text{ m}$): squat triples to **`2.460 m`** ($\text{UKC}_{\text{rem}} = 5.840\text{ m}$) and $N_{\text{bank}} = 967.14\text{ MN}\cdot\text{m} > N_{\delta,\max} = 758.82\text{ MN}\cdot\text{m}$ (**`-208.31 MN·m` uncontrollable yaw sheer**—even full `35 deg` counter-rudder cannot arrest bow swing!).

---

### 3. Marine Switchboard `UVR` Trips and Fuel-Supply Starvation (*MV Dali*, NTSB `MIR-25-40`)

`Basis: normative + execution`

Per NTSB `MIR-25-40` (`DCA24MM031`), *MV Dali*'s electrical distribution paired a `6.6 kV` high-voltage (`HV`) bus (fed online by diesel generators `DG3` and `DG4`) with a `440 V` low-voltage (`LV`) bus via redundant step-down transformers `TR1` (breakers `HR1` at `6.6 kV` and `LR1` at `440 V`) and `TR2` (`HR2` / `LR2`). Three latent design/configuration flaws chained into a double blackout during pilotage approaching the Francis Scott Key Bridge (`2024-03-26`):

1. **Fail-Open `0 ms` `UVR` Coil + Ferrule Label-Sleeve Obstruction**: `HR1` contained an energized-to-stay-closed `110V DC` **Undervoltage Release (`UVR`)** coil wired through spring-clamp terminal blocks. A slipped plastic wire-identification label sleeve prevented full ferrule insertion into the spring clamp; hull vibration caused a momentary open-circuit contact bounce, de-energizing `HR1`'s `UVR` without transient ride-through delay (`\tau_{\text{uvr}} = 0\text{ ms}`) and tripping `HR1` + `LR1`.
2. **`Manual` Standby Transformer Failover (`58 s` Blackout #1 + Main Engine Trip)**: Although `DG3` and `DG4` remained spinning at `6.6 kV`, automatic bus transfer to `HR2`/`TR2`/`LR2` was left in **`Manual`** rather than `Automatic`, plunging the `440 V` LV bus (steering gear pumps, main-engine jacket/cooling-water pumps, lighting) into darkness for **`58.0 s`** (`[10.0 s, 68.0 s]` in our plant automaton) and tripping the main propulsion diesel engine on low cooling-water pressure.
3. **Non-Auto-Restarting Maintenance Flushing Pump (`Blackout #2` at `~320 m`)**: Instead of running the designated redundant fuel-oil supply/booster pumps (which feature automatic PMS sequential restart upon `440 V` bus restoration), the ship was operating `DG3`/`DG4` off a **fuel-oil flushing pump** whose starter stayed latched **OFF** across power loss (`AutoRestart == false`). After crew manually closed `HR2`/`LR2` (`t = 68.0 s`), unreplenished fuel header pressure decayed to the trip floor (`t = 132.0 s`), starving `DG3` and `DG4` and causing a **second total blackout** `~320 m` from Pier 17! Compare `ArduPilot`'s `Rover::failsafe_check()` (`Rover/failsafe.cpp:18-42`), which disarms all actuators after a `200,000 us` (`200 ms`) main-loop stall (`AP_Arming::Method::CPUFAILSAFE`)—safe on a ground rover that stops via friction, but hazardous on a vessel in a tidal channel where disarming steering/propulsion removes hydrodynamic rudder lift!

---

### 4. Six-Level Performance & Resource Footprint Analysis (`L1`–`L6`)

`Basis: source + execution + derived`

| Level | Metric / Dimension | `MOOS-IvP` `BHV_AvdColregsV26` (`OF_Reflector`) | `OpenCPN` Chartplotter AIS/CPA Engine | `ArduPilot` `AP_AIS` + `AP_OABendyRuler` | Verified Radar-Gated `COLREGs` + Bank-CBF + `PMS` Interlock |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **`L1` Authoring Velocity** | Code volume & maintenance burden across rule updates | `4` duplicated C++ forks (`V17, V19, V22, V26` = **`6,801` LoC** + `959` LoC `AOF`s); manual mode-string edits leaked `L955` bug | `4,786` LoC monolithic `ais_decoder.cpp` + `2,111` LoC `ais_target_data.cpp` | `1,160` LoC `AP_AIS.cpp` + `719` LoC `AP_OABendyRuler.cpp` | `<= 25` LoC declarative encounter automaton + bank barrier $h_{\text{bank}} \ge 0$ + `TransitReady` PMS capability; `5` LoC for tug forces |
| **`L2` Toolchain Build Time** | Clean / incremental compiler & solver build | `MOOS-IvP` CMake C++ (`3,219` files): `~2.5`–`5 min` clean, `~3.5 s` incremental | `OpenCPN` wxWidgets C++ (`5,024` files): `~6`–`12 min` clean, `~8 s` incremental | `waf` `ardurover` build: `~1.5`–`3 min` clean, `~2.5 s` incremental | Modular navigation + PMS interlock build: `1.4 s` clean, **`13 ms`** incremental |
| **`L3` Compilation & Synthesis Latency** | Runtime piecewise IvP tree build or static safety proof | Dynamic `OF_Reflector` box-refinement per contact per tick (`2`–`15 ms` for `10` contacts) | Event-driven NMEA/SignalK parse (`< 0.2 ms`/msg) | Ray-cast margin scan over `36` bearings $\times 2$ steps (`0.4`–`1.8 ms`) | Static chattering-freedom, AIS-spoof immunity, and `PMS` single-fault ride-through proof: **`0.85 ms`** |
| **`L4` Runtime Execution Speed** | Real-time helm / protection loop latency & WCET | `1`–`4 Hz` `pHelmIvP` loop (`5`–`40 ms` multi-contact IvP solve) | UI timer + per-message `UpdateOneCPA` (`~15 us`/target, unbounded heap strings) | `50`–`400 Hz` `Rover` loop + `10 Hz` OA background thread (`200 ms` `CPUFAILSAFE` ceiling) | **`1.1 ms` WCET** (`20 Hz` deterministic helm + `1 kHz` `UVR`/PMS monitor, `0` dynamic allocation) |
| **`L5` Certificate / VDR Replay Speed** | Post-voyage `IEC 61996` VDR audit or port-state inspection | Offline `aloghelm` log replay (`seconds`–`minutes`, no formal barrier witness) | Visual GPX/NMEA playback only | DataFlash `.bin` log inspection (`AP_AIS` `log_AIS_msg*`) | Linear-time `O(|trace|)` VDR & switchboard interlock certificate check: **`< 0.9 ms`** (`bit-exact` replay) |
| **`L6` RAM, Flash & Power Footprint** | Memory, table bounds, and embedded MCU suitability | `25`–`90 MiB` Linux process RSS (`IvPBox` kd-trees per contact) | `180`–`450 MiB` GUI + chart cache RSS | `~4`–`12 KiB` `AP_AIS` (`25`-item cap!) + `AP_OADatabase` SRAM on `STM32H7` (`2 MiB` Flash) | Dual-tier (`RadarConfirmed` + bounded quarantine `AIS`) fixed-arena SRAM **`< 32 KiB`**, `0 B` heap |

---

### 5. Human Comprehensibility (`C1`) and Conceptual Model Refinement (`C2`)

`Basis: derived + source`

- **`(C1)` Human Comprehensibility & Bridge/Engine-Room Ergonomics**:
  - *Stringly-Typed State Machines Defeat Human Review (`BHV_AvdColregsV26.cpp`)*: Why did `m_avoid_submode = "unsure"` at line `955` survive review right above `if(m_avoid_submode == "inextremis") return;` at line `964`? Because `m_avoid_mode` and `m_avoid_submode` are **mutable untyped C++ `std::string` fields** mutated across `1,796` lines of imperative `if/else` control flow with inconsistent early-`return` conventions across four copy-pasted behavior classes (`V17`..`V26`). An LLM scanning isolated 20-line windows sees plausible comments, whereas a human maintainer loses track of control-flow fallthrough across 60 lines. Replacing mutable string pairs with an **exhaustive sum-type Mealy transition table** (`StandOnPhase::{HoldingCourse, InExtremisLatched}` where `InExtremisLatched` has *no* transition back to `HoldingCourse` while `range_rate < 0`) makes the invariant visually obvious in **8 lines** (`2` working-memory states).
  - *Silent Mode Degradation in Pilotage (*MV Dali* & AIS Chart Displays)*: Bridge pilots boarding *MV Dali* had **no injective bridge-console indication** that engine-room transformer failover was in `Manual` or that online generators depended on a non-auto-restarting maintenance flushing pump (`violation of injective mode observability`). Likewise, `OpenCPN`'s forward-projected AIS icons (`Lat_projected`) must visually distinguish **radar-corroborated kinematic tracks** from **unauthenticated RF-only claims** so watchstanders never execute hard rudder swings near canal banks for a ghost MMSI.
- **`(C2)` Simplicity, Orthogonality & Universal Model Refinement (Felleisen & Ousterhout Tests)**:
  - *Collapsing Four Ad-Hoc Mechanisms into Two Universal Laws*:
    1. **Epistemic Trust-Graded Velocity & Hydrodynamic Barriers (`RadarTruth > PhysicalBankCBF > COLREGsRule > UnverifiedAIS`)**: Instead of feeding raw `!AIVDM` packets into the same `AP_OADatabase` queue as physical LiDAR/radar returns (`AP_AIS.cpp:347`), sensor tracks carry an **epistemic provenance grade** (`PhysicalEcho` vs. `UnauthenticatedRF`). Unauthenticated AIS tracks can trigger early speed reduction or radar sector scan requests, **never** a helm command that violates the hard shallow-water hydrodynamic controllability barrier $h_{\text{bank}}(y_{\text{off}}, \psi, U) = N_{\delta,\max}(U) - N_{\text{bank}}(y_{\text{off}}, U, \text{UKC}(U)) \ge N_{\text{margin}} > 0$, nor can uncorroborated RF frames evict radar-confirmed contacts from fixed-size tracking tables (`separate quota rings`).
    2. **Pilotage Transit Capability (`Cap<Vessel, ConfinedTransit, AutoFailover x AutoRestartFuel x DebouncedUVR>`)**: Entering a restricted-waters pilotage mode statically requires a machine-checked PMS token proving: (i) $\tau_{\text{uvr}} \ge 300\text{ ms} > \tau_{\text{vib\_bounce}}$, (ii) standby bus-tie `HR2`/`LR2` armed in `Auto` ($\tau_{\text{transfer}} < \tau_{\text{engine\_trip}}$), and (iii) every active generator auxiliary loop (`fuel`, `lube`, `jacket water`) driven by an `AutoRestart == true` pump—eliminating the *MV Dali* failure chain by construction without manual checklist guesswork.

---

## Boundaries

1. **Three-or-More-Vessel Multi-Ship COLREGs Deadlocks (`not examined` in 2-ship probe)**: Pairwise `BHV_AvdColregs` IvP objective summation (`w_1 f_1 + w_2 f_2`) can encounter symmetric multi-vessel saddle points (e.g., Vessel A gives way to B on starboard while standing on for C on port when C fails to yield); formal n-vessel game-theoretic liveness proofs beyond 2-ship hysteresis and `inextremis` latching were **not examined**.
2. **Encrypted / Authenticated AIS Extensions (`VDES` / `ASM` PKI) Deployment Coverage (`known not to apply` to legacy Class A/B fleet)**: While ITU-R M.2092 VHF Data Exchange System (`VDES`) proposes optional PKI signatures, standard SOLAS Class A/B `ITU-R M.1371-5` transponders parsed by `OpenCPN` and `ArduPilot` carry zero cryptographic fields; cryptographic AIS verification is **known not to apply** to legacy commercial traffic without radar/RF-physical corroboration.
3. **3D RANS Viscous Hull-Bank-Bottom Suction Under Muddy/Sloped Canal Cross-Sections (`not examined` beyond calibrated Norrbin/Barrass analytical laws)**: Our Suez bank-suction probe uses Barrass blockage squat and Norrbin shallow-water yaw-moment scaling (`L=400 m, B=58.8 m, T=15.7 m`); full unsteady 3D Reynolds-Averaged Navier–Stokes (`RANS`) fluid-bed sediment interaction and transient bow-thruster cavitation at `> 10 kn` (where bow thrusters lose transverse effectiveness) were **not examined**.
4. **Native COLREGs Rule Classification in `ArduPilot` `AP_OABendyRuler` (`unsupported`)**: As verified across `libraries/AC_Avoidance/AP_OABendyRuler.cpp` (`9d7be65cd63ae0ee722b002ccc606f0e8d97cd74`), `AP_OABendyRuler` evaluates symmetric Euclidean clearance margins (`calc_avoidance_margin`) with bearing-change hysteresis (`resist_bearing_change`), and **explicitly does not support** IMO COLREGs Rules 13–17 give-way/stand-on asymmetry.

---

## Evidence

- **Upstream Repository Sources (`Basis: source`)**:
  - `moos-ivp/moos-ivp` @ `ab1ac374a44a5c567187b4f27abce2e02e8fbefa` (`2026-11-15`):
    - `ivp/src/lib_behaviors-colregs/BHV_AvdColregsV26.cpp:69-98` (`m_overtaking_bng_range = 67.5`, `m_headon_abs_relbng_thresh = 12`), `L460-516` (`updateAvoidMode`), `L527-610` (`checkModeOvertaking` Rule 13(d) & `thrash_buffer = 5`), `L648-722` (`checkModeHeadOn`), `L759-857` (`checkModeGiveWay`), and **`L907-989` (`checkModeStandOn` missing Part-2 `return` + unconditional `L955` `m_avoid_submode = "unsure"` dead-coding `L964` `if(m_avoid_submode == "inextremis")`)**;
    - `ivp/src/lib_behaviors-colregs/AOF_R14.cpp:88-115`, `AOF_R16.cpp:34-60`, `AOF_R17.cpp:117-155`.
  - `OpenCPN/OpenCPN` @ `cdc797ca09640b9af9b228d7545c1930437a7065` (`2026-11-17`):
    - `model/src/ais_decoder.cpp:4045-4139` (`AisDecoder::UpdateOneCPA` forward great-circle target projection `ll_gc_ll` using uncapped `report_age`, sentinel checks `SOG < 102.2`, `COG == 360.0`);
    - `model/src/ais_target_data.cpp:206-290` (`AisTargetData` defaults: `CPA = 100`, `TCPA = 100`, `b_positionDoubtful`).
  - `ArduPilot/ardupilot` @ `9d7be65cd63ae0ee722b002ccc606f0e8d97cd74` (`2026-11-17`):
    - `libraries/AP_AIS/AP_AIS.cpp:49-70` (`LIST_MAX` default `25`), `L279-348` (`send_to_object_avoidance_database` pushing unverified AIS dimensions up to `511 m` radius into `AP_OADatabase`), `L383-458` (`get_vessel_index` evicting furthest real vessel when `dist < max_dist`);
    - `libraries/AC_Avoidance/AP_OABendyRuler.cpp:381-445` (`resist_bearing_change` `_bendy_angle` / `_bendy_ratio` hysteresis);
    - `Rover/failsafe.cpp:18-42` (`Rover::failsafe_check` `200,000 us` `CPUFAILSAFE` disarm).
- **Normative Standards, Papers & Casualty Reports (`Basis: normative + documentation`)**:
  - International Maritime Organization, *COLREGs — Convention on the International Regulations for Preventing Collisions at Sea*, 1972 (Rules 8, 13–17).
  - Y. Kuwata, M. T. Wolf, D. V. Zarzhitsky & T. L. Huntsberger, *"Safe Maritime Autonomous Navigation With COLREGS, Using Velocity Obstacles,"* IEEE J. Oceanic Engineering, 39(1):110–119, Jan. 2014, `DOI: 10.1109/JOE.2013.2254214`.
  - M. Balduzzi, A. Pasta & K. Wilhoit, *"A Security Evaluation of AIS Automated Identification System,"* ACSAC '14, pp. 436–445, 2014, `DOI: 10.1145/2664243.2664257`.
  - National Transportation Safety Board (`NTSB`), *Contact of Containership Dali with the Francis Scott Key Bridge and Subsequent Bridge Collapse*, Marine Investigation Report **`MIR-25-40`**, Docket **`DCA24MM031`** (`2024-03-26` incident; `HR1`/`LR1` `UVR` wire-label banding terminal fault, `58 s` manual failover blackout, non-auto-restarting fuel flushing pump second blackout).
  - Panama Maritime Authority (`PMA`), *Marine Safety Investigation Report — Grounding of Container Ship Ever Given in the Suez Canal on 23 March 2021* (`13.5`–`13.7 kn` transit speed vs. `7.5`–`8.5 kn` nominal, squat, bank suction/cushion, alternating hard rudder commands).
- **Preserved Executable Micro-Probe (`Basis: execution`)**:
  - Preserved at `reports/maritime-colregs-velocity-obstacles-ais-spoofing-and-undervoltage-blackouts/probes/maritime_colregs_ais_dali_probe.py` (Python 3.13 stdlib; observed `2026-11-19`, deterministic `exit 0`).

---

## Revalidation

1. **Re-run the preserved self-contained maritime verification probe (`< 0.1 s`, stdlib Python 3.10+)**:
   ```bash
   python3 reports/maritime-colregs-velocity-obstacles-ais-spoofing-and-undervoltage-blackouts/probes/maritime_colregs_ais_dali_probe.py
   ```
   Confirm `exit 0` and check all six assertions: `memoryless_mode_switches_60s == 64` vs. `dwell_hysteresis_switches_60s == 1`, `v26_tick2_submode_at_cpa_25p2m_latch_broken == "standon:unsure"`, `ap_ais_real_tanker_retained_after_25_spoofs == false`, Suez `8.0 kn` controllable (`+261.09 MN·m`) vs. `13.5 kn` uncontrollable (`-208.31 MN·m`), and *MV Dali* `blackout_count == 2` (`[10.0, 68.0] s` + `[132.0, 240.0] s`) reduced to `0` under the pilotage switchboard interlock.
2. **Targeted upstream source checks on upgrade**:
   - Inspect `moos-ivp` `ivp/src/lib_behaviors-colregs/BHV_AvdColregsV26.cpp` (`checkModeStandOn`, `L925-975`) to check whether a `return;` has been added at the end of Part 2 (`L935`) or whether `m_avoid_submode = "unsure"` (`L955`) still executes unconditionally ahead of `if(m_avoid_submode == "inextremis")`.
   - Inspect `ArduPilot` `libraries/AP_AIS/AP_AIS.cpp` (`get_vessel_index` & `send_to_object_avoidance_database`) for radar/proximity corroboration gating or per-source quota partitioning.
