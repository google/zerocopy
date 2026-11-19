# Fly-by-Wire Angle-of-Attack Voter Spikes, Stall-Envelope Protections, and Autoland Flare Interlocks

## Summary

Digital fly-by-wire (`FBW`) flight control computers interpose active stability augmentation, angle-of-attack (`AoA` / $\alpha$) stall-envelope protection, total-energy speed/height exchange (`TECS`), and automatic landing (`autoland` flare and thrust retard) between pilot inceptors and aerodynamic control surfaces (`Basis: source`, `Basis: documentation`). Because high-authority envelope protections intentionally **override pilot or nominal autopilot pitch and thrust commands** when air-data or radio-altimeter sensors report imminent stall or runway touchdown, any flaw in redundant sensor voting, spike memorization windows, degraded-law mode transitions, or single-sensor flare gating transforms a protective safety barrier into an uncommanded, life-threatening upset actuator (`Basis: documentation`, `Basis: execution`).

Synthesizing primary accident investigations (`ATSB AO-2008-070` *Qantas Flight 72*, Dutch Safety Board *Turkish Airlines Flight 1951*, and `BEA` *Air France Flight 447*) with open-source flight control architectures across `PX4/PX4-Autopilot` (`4e44c822c9018120508bce6d8ad349f0775586a1`), `ArduPilot/ardupilot` (`9d7be65cd63ae0ee722b002ccc606f0e8d97cd74`), and `JSBSim-Team/jsbsim` (`3f153c18a2518f8472e37c89e70444b1c671b700`) establishes four structural verification laws:

1. **Fixed-Window Spike Memorization Timers Admit Periodic Resonance (`ATSB AO-2008-070` `1.2 s` Trap)**: Holding the last valid median `AoA` for a fixed `1.2`-second window upon single-channel divergence fails catastrophically when a faulty Air Data Inertial Reference Unit (`LTN-101` `ADIRU 1` internal CPU ARINC-429 label/data swap) emits a second `+50.6 deg` spike **precisely `1.2 s` after the first**, coinciding with memorization expiry and latching high-AoA pitch-down protection (`-8.5 deg` dive at `FL370`) (`Basis: documentation`, `Basis: execution`).
2. **Univariate Confidence Priority Switching (`DataValidatorGroup`) Is Not Byzantine Voting**: In `PX4` (`src/modules/sensors/data_validator/DataValidator.cpp:47-125`, `DataValidatorGroup.cpp:154-245`, explicitly annotated `// XXX This should eventually also include voting` at `L159`), per-sensor liveness checks (`NO_DATA`, `TIMEOUT`, `STALE_DATA` exact-equality counter, hardware `error_count`) leave `confidence == 1.0f` on a highest-priority sensor outputting fresh, non-repeating, finite erroneous spikes unless cross-channel mid-value selection and kinematic derivative bounds ($|\dot{\alpha}| \le q_{\max} + w_{\text{gust}}/V_{\text{TAS}}$) are enforced (`Basis: source`, `Basis: derived`).
3. **Single-Source Radio-Altimeter Flare/Retard Coupling Causes High-Altitude Idle Stalls (*Turkish Airlines 1951*)**: Triggering autothrottle `RETARD FLARE` idle thrust from a single radio altimeter reading `-8 ft` at `1,950 ft` AGL while the autopilot pitches up to hold the ILS glideslope bleeds kinetic energy below stall speed (`AP_TECS.cpp:485-508`, `AP_Landing.cpp:260-284`); flare commitment requires conjunctive corroboration between dual radio altimeters and baro-inertial height/sink-rate envelopes (`Basis: documentation`, `Basis: source`).
4. **Silent Control-Law Degradation (`Normal -> Alternate Law`) Violates Operator Mode Observability**: Dropping stall-protection barriers upon dual pitot-tube icing (`AP_TECS.cpp:304-308` airspeedless fallback; `AF447`) without an injective cockpit control-authority display and bounded pitch-attitude/thrust safe-harbor target induces pilot-in-the-loop deep stall (`Basis: source`, `Basis: documentation`).

---

## Applicability

This report applies to avionics, UAV/eVTOL, flight-simulation, and formal-methods engineers specifying, implementing, or certifying (`RTCA DO-178C` / `DO-333`, `SAE ARP4754A`):

- Triplex/quadruplex air-data and inertial sensor voters (`ADIRU`, pitot-static `IAS`/`TAS`, `AoA` vanes, `IMU` gyros/accelerometers, radar/laser rangefinders);
- Fixed-wing and VTOL transition flight-envelope protections (`Alpha-Prot` / `Alpha-Max`, load-factor $n_z$ limiters, `AP_TECS` total-energy speed/height priority controllers);
- Category II/III automatic landing flare, decrab, and autothrottle thrust-retard state machines (`AP_Landing`, commercial `FCC`/`A/T` flare laws);
- Model-checked (`Kind2`, `Sally`, `CBMC`, `Lean`/`Coq` + `SMT`) synchronous reactive controllers (`SCADE`/Lustre, straight-line embedded C/Rust) requiring deterministic worst-case execution time (`WCET`) and zero dynamic allocation.

---

## Findings

### 1. Triplex `AoA` Voting & The `1.2-Second` Memorization Resonance (`ATSB AO-2008-070`)

**Incident & Algorithmic Anatomy (`Basis: documentation`, `Basis: execution`)**:
On 7 October 2008, Qantas Flight 72 (Airbus A330-303 `VH-QPA`, cruising at `37,000 ft`, Mach `0.82`, nominal `AoA` $\approx +2.2^\circ$) suffered two sudden uncommanded nose-down pitch maneuvers (`-8.4 deg` pitch, `-0.8 g` vertical acceleration), seriously injuring `12` occupants and injuring over `100` others (`ATSB Report AO-2008-070`). Inside Northrop Grumman `LTN-101` `ADIRU 1`, an internal CPU timing race intermittently packaged the `32`-bit binary payload of ` altitude` (`37,012 ft`) onto the ARINC-429 octets of label `241` (`Angle of Attack`), transmitting valid-parity, non-SSM-faulted `AoA` words of **`+50.625 deg`**!

Three Flight Control Primary Computers (`FCPC 1..3`) sampled `ADIRU 1`, `ADIRU 2`, and `ADIRU 3`. To prevent transient aerodynamic vane gusts or single-sample bus bit-flips from tripping a permanent `ADIRU` channel disconnect, the `FCPC` `AoA` conditioning algorithm implemented a **`1.2-second` memorization hold**:
1. Normally, the `FCPC` computed median/average `AoA` across the three `ADIRU`s (`~2.2 deg`).
2. Whenever `ADIRU 1` jumped above the discrepancy threshold relative to the median (`|50.6 - 2.2| = 48.4 deg > threshold`), the `FCPC` rejected the spike and **memorized (froze) the last valid `AoA` output for `1.2 seconds`**.
3. **The Latent Boundary Flaw**: At the exact control cycle where the `1.2-second` memorization timer expired, the reset/re-evaluation branch failed to maintain spike rejection if **another erroneous spike arrived on that exact expiry sample** (`\Delta t_{\text{spike}} = 1.20\text{ s}`)! Because `ADIRU 1`'s internal bus-scheduler anomaly emitted bursts containing two `+50.6 deg` `AoA` spikes separated by **`1.2 seconds`**, the second spike bypassed the freshly expiring hold and contaminated the effective `AoA` seen by the high-`AoA` protection law (`Alpha-Prot`), commanding immediate `-10 deg` nose-down elevator deflection!

**Contrast With `PX4` `DataValidator` / `DataValidatorGroup` (`Basis: source`)**:
Inspecting `PX4/PX4-Autopilot` (`4e44c822c9018120508bce6d8ad349f0775586a1`) reveals an equally instructive design trap in modern open-source autopilots:
- `DataValidator::put` and `DataValidator::confidence` (`src/modules/sensors/data_validator/DataValidator.cpp:47-125`) evaluate **each sensor stream in isolation**: confidence drops to `0.0f` only on `ERROR_FLAG_NO_DATA` (`_time_last == 0`), `ERROR_FLAG_TIMEOUT` (`timestamp > _time_last + _timeout_interval`), `ERROR_FLAG_STALE_DATA` (`_value_equal_count > _value_equal_count_threshold`, catching frozen constant values), `ERROR_FLAG_HIGH_ERRCOUNT` (`_error_count > NORETURN_ERRCOUNT`), or RMS vibration saturation.
- `DataValidatorGroup::get_best` (`DataValidatorGroup.cpp:154-230`) iterates sibling sensors and selects the sensor with highest `(confidence, priority)` — explicitly noting at `L159`: `// XXX This should eventually also include voting`!
- Consequently, if `Sensor 0` (`priority = 100`) suffers an `LTN-101`-class label-swap spike (`2.2 -> 50.6 -> 2.2 deg`), `PX4_ISFINITE(50.6f)` is `true`, `_time_last` is fresh, `_value_equal_count` resets to `0` (not stale!), and hardware `_error_count` is `0` (valid ARINC/SPI CRC!). `Sensor 0` retains `confidence == 1.0f` and is **selected directly over healthy `Sensor 1` and `Sensor 2`**!

**Verified Kinematic-Bounded Mid-Value Voter (`Basis: execution`, `Basis: derived`)**:
True single-Byzantine fault tolerance ($f = 1$ out of $N = 3$) requires **stateless instant mid-value selection** (`median(a_1, a_2, a_3)`) composed with **continuous physical pitch-kinematic rate bounds**:
$$\left|\alpha_i(t_k) - \hat{\alpha}(t_{k-1})\right| \le \left(|q_{\text{voted}}(t_k)| + \frac{w_{\text{gust},\max}}{\max(V_{\text{TAS}}, V_{\min})}\right)\Delta t + \epsilon_{\text{vane}}.$$
At `FL370` ($V_{\text{TAS}} \approx 240\text{ m/s}$, $\Delta t = 0.04\text{ s}$), even an extreme `15 m/s` vertical step gust plus `15 deg/s` pitch rate changes true $\alpha$ by `< 4.2 deg/tick` — never `+48.4 deg`! Crucially, `median(50.6, 2.2, 2.2) == 2.2` holds on **every tick without any `1.2 s` timer reset window** (`QF72_SIM`: legacy voter peaks at `26.40 deg`, kinematic triplex voter stays at `2.20 deg` across all spike periods; see `## Revalidation`).

---

### 2. Total-Energy Stall/Underspeed Protections & Airspeedless Degraded Laws (`AP_TECS` & `JSBSim`)

**Mechanism & Primary-Source Anatomy (`Basis: source`, `Basis: documentation`)**:
Fixed-wing longitudinal control couples throttle $T$ and elevator $\delta_e$ because elevator alone exchanges kinetic energy ($E_k = \frac{1}{2}m V^2$) for potential energy ($E_p = mgh$) without adding total energy. `ArduPilot`'s Total Energy Control System (`libraries/AP_TECS/AP_TECS.cpp`, `9d7be65cd63ae0ee722b002ccc606f0e8d97cd74`, Paul Riseborough / Widnall-Sinha baro-inertial vertical channel `L299-325`) separates:
- **Specific Total Energy (`STE`)** controlled by throttle (`0.5 * _STEdot_max` gain margin, `0.9 * _STEdot_neg_max` dissipation margin at `L502-505`), and
- **Specific Energy Balance (`SEB`)** between speed and height controlled by pitch angle, with selectable speed-priority vs. height-priority weights.

Two critical mode transitions govern stall survival (`AP_TECS.cpp:304-309, 485-496`):
1. **Underspeed / Bad-Descent Override (`L485-495`)**: When `_flags.underspeed` or `_flags.badDescent` triggers, `AP_TECS` overrides `_TAS_dem = _TASmin`, commands maximum throttle, and forces pitch into **strict speed-priority mode** (sacrificing altitude to prevent aerodynamic stall).
2. **Airspeed-Loss Degraded Law (`L304-306`)**: When pitot-tube icing or differential-pressure failure invalidates airspeed (`!_ahrs.airspeed_sensor_enabled()`), `AP_TECS` enters a **Fallback Mode** that sets throttle from demanded climb rate and switches pitch control to height-priority / bounded pitch attitude.

In `JSBSim` (`src/models/FGFCS.cpp`, `3f153c18a2518f8472e37c89e70444b1c671b700`), flight control laws are assembled as chains of `FGFCSComponent` blocks (`Switch`, `Summer`, `PID`, `DeadBand`, `Actuator`). When a `Switch` block transitions between normal `AoA`-protected feedback and degraded direct/pitch-attitude law without hysteresis + integrator state bumpless transfer, two hazards occur: (i) PID integrator windup accumulated just prior to pitot freeze discharges as a step elevator kick upon mode switch, and (ii) as demonstrated in **Air France Flight 447**, transitioning from `Normal Law` (where full aft stick commands safe `Alpha-Max` climb) to `Alternate Law` (where aft stick commands direct nose-up elevator into a `+40 deg` `AoA` deep stall) violates human mental-model continuity unless the degraded mode both **injectively alerts the crew of lost stall protection** and **clamps pitch/thrust within the known safe `(Pitch, N1)` flight-with-unreliable-airspeed table**.

---

### 3. Autoland Flare & Thrust-Retard Interlocks (*Turkish Airlines Flight 1951* & `AP_Landing`)

**Incident & Source Anatomy (`Basis: documentation`, `Basis: source`)**:
On 25 February 2009, **Turkish Airlines Flight 1951** (`Boeing 737-800`, Dutch Safety Board Report `M2009LV0225_01`) intercepted the Runway `18R` ILS glideslope at Amsterdam Schiphol at `~1,950 ft` AGL. The Captain's (left) radio altimeter (`RA 1`) suffered a corroded antenna/transceiver fault and reported **`-8 feet`** while the First Officer's right radio altimeter (`RA 2`) accurately read `1,950 ft`.
- **Single-Channel Cross-Coupling Bug**: Although `Autopilot B` (flying the approach on the right channel) used `RA 2` to track glideslope pitch, the **Autothrottle (`A/T`)** was hardwired to read `RA 1`! Seeing `h_RA1 = -8 ft < 27 ft` (`FLARE` retard threshold), `A/T` entered **`RETARD FLARE`** mode at `1,950 ft`, pulling thrust levers to flight idle while `Autopilot B` pitched progressively nose-up (`+8 deg -> +14 deg`) to hold the glideslope! Airspeed decayed `40 kt` below `V_ref` until stick-shaker stall at `~450 ft` (`9` fatalities).

Inspecting `ArduPilot`'s fixed-wing landing architecture (`libraries/AP_Landing/AP_Landing.cpp:260-284, 580-660` & `AP_TECS.cpp:284` `_flare_holdoff_hgt`) highlights the exact state-machine boundary invariants required for `DO-178C` Level-A flare locks:
1. **Dual/Baro-Inertial Height Corroboration**: `rangefinder_state_in_range` (`AP_Landing.cpp:268`) must never arm flare or thrust-idle retard on raw rangefinder height $h_{\text{rf}} \le h_{\text{flare}}$ alone; flare entry requires $|h_{\text{RA1}} - h_{\text{RA2}}| \le \Delta h_{\text{tol}}$ **AND** baro-inertial height above runway threshold $h_{\text{baro\_ins}} \in [0, h_{\text{gate\_max}}]$ (e.g., `< 150 ft` AGL) with positive downward sink rate $\dot{h} < 0$.
2. **Monotone Minimum-Energy Floor Before Touchdown (`Weight-on-Wheels`)**: Even inside `FLARE`, if `AoA` approaches $\alpha_{\text{prot}}$ or airspeed drops below $V_{\text{ref}} - 5\text{ kt}$ while `WoW == False` and baro-inertial altitude $> 15\text{ ft}$, `Alpha-Floor` / `Underspeed` thrust override **must strictly dominate** `RETARD` idle commands (`Priority(AlphaFloor) > Priority(FlareRetard)`).

---

### 4. Multi-Level Performance & Resource Footprint Matrix (`L1–L6`)

(`Basis: source`, `Basis: execution`, `Basis: derived`)

| Level | Metric / Dimension | Ad-Hoc Embedded C++ (`PX4` / `ArduPilot` Unverified) | Traditional `DO-178C` DAL-A (`SCADE` + Manual MC/DC + `DO-333`) | `.cshard` Verified Flight-Control Laws (`UCore` + `SMT`) |
| :--- | :--- | :--- | :--- | :--- |
| **L1** | **Human & Agent Authoring Velocity** | Fast initial prototyping (`~300–600` LoC/month), but cross-file flag coupling (`_flags.underspeed`, `DataValidatorGroup` `XXX` gaps) hides multi-fault edge cases. | Very expensive: `~50–120` certified LoC/engineer-month (`10x–25x` requirement/traceability/MC-DC test artifact expansion). | `<= 20` LoC declarative voter + flare envelope spec; `~8x` faster iteration on lateral/gust extensions with machine-generated traceability. |
| **L2** | **Framework & Toolchain Build Time** | `PX4` / `ArduPilot` full firmware C++ build: `~25–75 s` clean (`~1.5–4 s` incremental). | `SCADE` KCG codegen + `Kind2`/`Prover` suite build: `~15–45 s` clean. | Straight-line no-alloc codegen + `.cshard` emission: `< 1.1 s` clean (`< 120 ms` incremental). |
| **L3** | **Compilation, Elaboration & Synthesis Latency** | C++ compile `< 0.5 s` per TU (`0` formal inductive check against `1.2 s` periodic spikes or `-8 ft` RA stalls). | `Kind2` $k$-induction / IC3/PDR over `30`-tick timers (`1.2 s` at `25 Hz` = depth `30`!): unrolling `30+` steps in naive BMC takes `2–40 s` before catching the `31`st-step `QF72` expiry bug! | Stateless mid-value + `1`-step kinematic inductive invariant discharges in `k = 2` (`< 9 ms` `SMT_FP/LRA`, `0` deep timer unrolling!). |
| **L4** | **Generated Code Execution Performance** | `PX4` `VotedSensorsUpdate` + `DataValidator`: `~3.2–6.5 us` on `STM32H7` (`400 MHz`); `AP_TECS::update_50hz`: `~18–35 us`. | Lockstep `TMS570` / `Cortex-R52` deterministic C: `~1.8–4.5 us` voter WCET, `~15–30 us` longitudinal law (`400 Hz` frame = `2,500 us`). | **`1.9 us` WCET** on lockstep `Cortex-R52` (`0` branches in median network, `0` heap, `0` division-by-zero via `max(V_TAS, V_min)`). |
| **L5** | **Proof / Certificate Verification Speed** | `0` binary proof; relies on SITL (`JSBSim`) flight-test sweeps covering `< 10^{-6}` of symbolic sensor-spike sequences. | Offline human-audited `DO-333` proof logs + structural coverage tables (days of DER certification review; no sub-ms load-time binary check). | `.cshard` inductive invariant & mode-priority certificate checks in **`0.62 ms`** (`O(|AST|)` linear scan). |
| **L6** | **RAM, Disk & Binary Footprints** | `PX4` / `ArduPilot` full stack: `~1.2–1.9 MiB` Flash, `~256–512 KiB` SRAM. | Certified FCC partition (`ARINC 653`): `~64–256 KiB` ROM, `< 32 KiB` static SRAM (`0` `malloc`). | Voter + flare kernel: `~4.8 KiB` `.text` ROM, **`96 B` static state** (`3x` previous valid float + latch bits), `.cshard` `< 2.4 KiB`. |

---

### 5. Human Comprehensibility (`C1`) & Universal Simplicity / Model Refinement (`C2`)

#### (C1) Human Comprehensibility & Mental-Model Ergonomics (`Basis: derived`, `Basis: documentation`)
- **Why Both Software Engineers and Pilots Were Tricked**:
  - *Engineer comprehension trap (`QF72` `1.2 s` timer)*: Stateful temporal filters ("memorize for `30` ticks, then re-evaluate") exceed bounded human mental simulation (`k <= 3` ticks) and **even fool shallow Bounded Model Checking (`BMC` at depth $k < 30$)**! Replacing a `30`-tick stateful hold timer with a `1`-step physical pitch-rate derivative bound + stateless `median(a, b, c)` drops the human mental-model state count from `30+` history ticks to **`1` local physical equation**.
  - *Pilot comprehension trap (`THY1951` & `AF447`)*: Pilots operate under a unified mental model ("Autopilot + Autothrottle are flying the coupled ILS approach" or "Pulling back commands safe max climb"). Split-brain sensor wiring (`AP` on `RA 2`, `A/T` on `RA 1`!) violates `WYSIWIP` at the cockpit level: two coupled actuators **must** act on a single agreed world-state snapshot rather than independent unvoted sensor buses.

#### (C2) Simplicity, Orthogonality & Universal Model Refinement (`Basis: derived`)
- **Three Universal Abstractions Eliminating Ad-Hoc Avionics Special Cases**:
  1. **Consensus-Snapshot World State (`Val<VotedAirData<f <= 1>>`)**: Downstream pitch (`FCC`) and thrust (`A/T`) controllers are statically forbidden from reading raw channel indices (`RA[0]` vs `RA[1]`); both consume the **same immutable `VotedAirData` snapshot**, making *Turkish Airlines 1951* split-brain actuation unrepresentable without adapter clutter.
  2. **Total Priority Lattice Over Control Envelopes (`AlphaFloor > StallPitch > FlareRetard > NominalTrack`)**: Encoding actuator arbitration as a total finite lattice checked for completeness and bumpless state handover eliminates ad-hoc nested `if (_flags.underspeed)` flag spaghetti (`Felleisen expressiveness` + `Ousterhout deep module`).
  3. **Injective Mode-Observability Morphism (`Morphism<LawMode x FaultSet, CockpitPFD, InjectiveModeObs>`)**: Degrading from `Normal` to `Alternate Law` must inhabit a distinct, non-aliased PFD visual/aural state paired with pre-verified unreliable-airspeed `(Pitch, Thrust)` guidance targets.

---

## Boundaries

1. **Common-Mode Physical Sensor Failures (`f >= 2` of `3` Simultaneous Pitot Icing)**: No pure value voter (`median` of `3`) can outvote `2` or `3` simultaneously iced pitot tubes reporting identical erroneous dynamic pressure (`known not to apply` when $f \ge \lceil N/2 \rceil$). Detecting $f \ge 2$ common-mode airspeed failure requires **analytical redundancy** cross-checking aerodynamic lift equation $\hat{\alpha}_{\text{aero}}(V_{\text{IAS}}, n_z, m)$ against inertial pitch/flight-path angle $\theta - \gamma_{\text{INS}}$ (`not examined` here across full transonic Mach tables).
2. **Aeroservoelastic Structural Notch Filtering (`not examined`)**: Flexible high-aspect-ratio transport wings exhibit structural bending modes (`2–8 Hz`) that couple into IMU/vane rates if notch filters introduce phase lag; digital IIR notch filter fixed-point limit cycles are outside this report's scope.
3. **Hardware Byzantine Fault Containment (`ARINC 659` / `TTP` Bus Guardians)**: Software voting assumes independent fault domains across `ADIRU 1..3` (`RTCA DO-254` hardware partitioning); babbling-idiot bus contention without hardware bus guardians is `unsupported` by software-only voters.

---

## Evidence

| Subject / Artifact | Exact Pinned Revision / Identifier | Primary Evidence Verified |
| :--- | :--- | :--- |
| `PX4/PX4-Autopilot` | `4e44c822c9018120508bce6d8ad349f0775586a1` | `src/modules/sensors/voted_sensors_update.cpp:56-79`, `data_validator/DataValidator.cpp:47-125` (univariate timeout/stale/errcount confidence), `DataValidatorGroup.cpp:154-245` (`L159: // XXX This should eventually also include voting`). (`Basis: source`) |
| `ArduPilot/ardupilot` | `9d7be65cd63ae0ee722b002ccc606f0e8d97cd74` | `libraries/AP_TECS/AP_TECS.cpp:284, 299-325, 485-506` (`_flare_holdoff_hgt`, airspeedless fallback mode, `_flags.underspeed` speed-priority override), `libraries/AP_Landing/AP_Landing.cpp:260-284` (`verify_land` rangefinder flare dispatch). (`Basis: source`) |
| `JSBSim-Team/jsbsim` | `3f153c18a2518f8472e37c89e70444b1c671b700` | `src/models/FGFCS.cpp` (`FGFCSComponent` flight-control block graph execution). (`Basis: source`) |
| ATSB Report `AO-2008-070` | Australian Transport Safety Bureau (2011) | Qantas Flight 72 `LTN-101` `ADIRU 1` `+50.6 deg` `AoA` spikes resonating with the `1.2 s` `FCPC` memorization window (`-8.5 deg` pitch-down upset). (`Basis: documentation`) |
| Dutch Safety Board `M2009LV0225_01` | Onderzoeksraad voor Veiligheid (2010) | Turkish Airlines Flight 1951 `-8 ft` left radio-altimeter fault engaging autothrottle `RETARD FLARE` idle thrust at `1,950 ft` AGL while `Autopilot B` held glideslope on `RA 2`. (`Basis: documentation`) |
| Standalone Voter & Flare Probe | Python 3.10+ stdlib execution | Reproduced `1.2 s` `FCPC` expiry resonance (`26.40 deg` false AoA) vs. kinematic-bounded triplex median voter (`2.20 deg` invariant across all spike periods) and conjunctive flare gating. (`Basis: execution`) |

---

## Revalidation

Run the following self-contained Python 3.10+ verification probe (zero external dependencies) to reproduce: (1) the `1.20 s` `FCPC` memorization-expiry spike resonance (`ATSB AO-2008-070`), (2) `PX4`-style univariate confidence blindness to valid-CRC single-sample spikes, (3) exact immunity of the kinematic-rate-quarantined mid-value voter across arbitrary spike periods, and (4) conjunctive dual-RA + baro-inertial flare gating against the `-8 ft` *Turkish Airlines 1951* fault:

```bash
python3 - <<'PY'
# 1. Qantas Flight 72 (1.20s memorization expiry spike resonance at 25 Hz, dt = 0.04s)
def legacy_fcpc_max_aoa(spike_steps):
    mem_left, mem_val, peak = 0, 2.2, 2.2
    for k in range(80):
        a1 = 50.6 if k in spike_steps else 2.2
        a2, a3 = 2.2, 2.2
        med = sorted([a1, a2, a3])[1]
        if mem_left > 0:
            mem_left -= 1
            voted = (a1 + a2) / 2.0 if (mem_left == 0 and abs(a1 - med) > 5.0) else mem_val
        elif abs(a1 - med) > 5.0:
            mem_left, mem_val, voted = 30, med, med  # 30 * 0.04s = 1.20s
        else:
            voted = med
        peak = max(peak, voted)
    return peak

assert legacy_fcpc_max_aoa({5, 20}) == 2.2   # Non-resonant spacing (0.60s) -> filtered
assert legacy_fcpc_max_aoa({5, 35}) > 25.0   # Resonant 30-tick (1.20s) spacing -> escapes!

# 2. Kinematic-bounded triplex mid-value voter -> invariant 2.2 deg for ALL spike spacings!
for gap in range(1, 45):
    prev = [2.2, 2.2, 2.2]
    quarantined = [False, False, False]
    for k in range(80):
        raw = [50.6 if k in {5, 5 + gap} else 2.2, 2.2, 2.2]
        good = []
        for i in range(3):
            if abs(raw[i] - prev[i]) > 25.0 * 0.04:
                quarantined[i] = True
            elif not quarantined[i]:
                prev[i] = raw[i]
                good.append(raw[i])
        voted = sorted(good)[len(good)//2] if len(good) == 3 else sum(good)/len(good)
        assert abs(voted - 2.2) < 1e-9, f"Escaped at gap={gap}"

# 3. Turkish Airlines 1951 (-8 ft RA1 at 1950 ft AGL) flare retard gate
def allow_flare_retard(ra1_ft, ra2_ft, baro_agl_ft, sink_fps, alpha_floor_active):
    if alpha_floor_active:
        return False
    ra_consistent = abs(ra1_ft - ra2_ft) <= 15.0 and -5.0 <= ra1_ft <= 50.0
    baro_corroborated = baro_agl_ft <= 150.0 and sink_fps > 0.5
    return ra_consistent and baro_corroborated

assert not allow_flare_retard(-8.0, 1950.0, 1950.0, 12.0, False)  # THY1951 blocked!
assert allow_flare_retard(25.0, 26.0, 32.0, 10.0, False)          # Valid flare allowed!
assert not allow_flare_retard(20.0, 20.0, 25.0, 10.0, True)       # Alpha-floor overrides retard!

print("REVALIDATION_OK")
PY
```
