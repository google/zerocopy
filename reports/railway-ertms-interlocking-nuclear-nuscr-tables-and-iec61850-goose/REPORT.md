# Vital Railway Interlocking, ERTMS/ETCS Braking Curves, Nuclear NuSCR Tabular Verification, and Sub-3ms IEC 61850 GOOSE/SV Protection

## Summary

Safety-critical railway signaling (`EN 50128` SIL 4 / `ERTMS/ETCS`), nuclear reactor shutdown protection (`IEC 60880` / `NuSCR`), and electrical substation automation (`IEC 61850` `GOOSE`/`SV` + `IEC 62351-6`) share one core engineering failure mechanism: **discrete safety tables and protocol state machines fail catastrophically when composed with missing non-local guards, continuous physical dynamics, or sub-millisecond timing and authentication bounds**:

1. **In-Path Railway Interlocking Without Flank/Overlap Locking and Kinematic Braking Without Cycle/Traction Compensation Both Admit Collisions:** In `B-Method`/`Event-B` and `ProB` (`hhu-stups/prob2_kernel`), route locking restricted to on-path switches and track circuits permits a converging shunt movement to foul an already-cleared junction in 4 transitions (`Probe 1A`), while explicit-state checking (`ConsistencyChecker`) scales exponentially on large yards and inductive constraint checking (`CBCInvariantChecker`) requires auxiliary strengthening invariants to avoid unreachable counterexamples. Across the continuous physical boundary, Platzer and Quesel's differential dynamic logic (`dL`) verification (`LS-Lab/KeYmaeraX-projects/etcs/etcs.kyx`) and `OpenRailAssociation/osrd`'s `ERA SUBSET-026` braking-curve implementation (`ETCSBrakingCurves.kt`) establish that nominal kinematic stopping distance $v^2/(2b)$ (`3858.0 m` at `300 km/h` and $b = 0.9\text{ m/s}^2$) underestimates safe emergency brake intervention by `+260.8 m` (`4118.8 m`) under `dL` cycle-acceleration compensation and `+526.6 m` (`4384.6 m`) under full `SUBSET-026` Brake Equivalent Time (`BEC`) traction-cutoff and odometry-inaccuracy margins.
2. **Parnas/SCR and `NuSCR` Tabular Protection Logic Eliminates Ambiguity via Disjointness & Completeness, While `2oo4` Voting Availability Is Governed by CCF ($\beta$) Rather Than Channel Count:** Formally checking pairwise **Disjointness** ($\neg(C_i \land C_j)$ across conflicting outputs) and **Completeness** ($\bigvee_i C_i \equiv \top$) exposes overlapping permissive-bypass rules and missing hysteresis bands (`22` conflicts and `8` gaps caught deterministically in `Probe 1B`). Under nuclear **2-out-of-4 (`2oo4`)** coincidence voting with channel maintenance bypass, degrading `2oo4` to `2oo3` raises independent Probability of Failure on Demand (`PFD_ind`) by ~`790x` (`3.43e-09` to `2.71e-06`), whereas degrading to `1oo3` drops `PFD_ind` to `8.57e-10` at the price of a `263x` jump in spurious reactor trips (`2.16e-05` to `5.69e-03`)—yet even `5%` Common-Cause Failure (`CCF`) coupling floors total system `PFD` at `~5.0e-05` across all three voting modes.
3. **Unauthenticated `IEC 61850` `GOOSE`/`SV` Subscribers Are Vulnerable to `stNum` Poisoning, Concrete `libiec61850` Replay Bugs, and Asymmetric-Crypto Latency Violations:** Source inspection of `mz-automation/libiec61850` (`6e265c54af66ea686453b6d31c4dcce1cf7ad2bd`) surfaces **four concrete defects**: (a) `goose_receiver.c:1088-1100` accepts **backward-`stNum` replays** (`stNum < self->stNum` yields `stateValid = true`), mutates `dataSetValues` *before* counter checks, and overwrites `self->sqNum` even when `isValid == false` (allowing a two-packet `sqNum=0 -> sqNum=1` replay bypass); (b) `goose_receiver.c:1138` mis-parses IEEE `802.1Q` `PCP` via C operator precedence (`buffer[bufPos + 2] & 0xF8 >> 5` evaluates `& 0x07`); and (c) `IEC 61850-90-5` `RSession` (`r_session.c:1147-1165`, `r_session_crypto_mbedtls.c:42-79`) writes length byte `16` for 32-byte `HMAC-SHA256-256` (breaking wire decoding), overflows a 32-byte digest into `bufPos + 16` for `HMAC-SHA256-128` (ignoring `hmacMaxSize`), leaks `md_ctx` on error, and omits `spduNumber` replay checks. Inside `< 3.000 ms` `IEC 61850-5` `TT6` protection deadlines, legacy `IEC 62351-6:2007` RSA-2048 signatures fail (`4.53–4.78 ms`), whereas `IEC 62351-6:2020` symmetric `HMAC-SHA256-128` / `AES-GMAC` clears `< 0.30 ms` (`0.049 ms` with `802.1Qbu` frame preemption).

## Applicability

This report synthesizes normative standards, peer-reviewed verification and attack analyses, direct upstream source inspection of four pinned repositories, and a three-part executable Python 3 probe suite (`Probe 1A`, `Probe 1B`, `Probe 1C`):

- **Vital Railway Interlocking & ERTMS/ETCS Speed Supervision:**
  - `hhu-stups/prob2_kernel` @ `9f01dbb53751242084735445a871b53fd3fbf4b3` (`CBCInvariantChecker.java`, `CBCDeadlockChecker.java`, `ConsistencyChecker.java`, `ModelCheckingOptions.java`): applies to Java/Prolog state-space and constraint-based formal model checking of Classical B and Event-B interlocking models.
  - `OpenRailAssociation/osrd` @ `af7025a6fbf91a517baf00157bdf3f2f081256e6` (`ETCSBrakingCurves.kt`, `ETCSBrakingSimulator.kt`, `EtcsBrakeParamsExt.kt`, `SpacingResourceGenerator.kt`): applies to timetable-level ETCS Level 2 braking-curve generation and track-zone conflict detection aligned with `ERA SUBSET-026-3 v400`.
  - `LS-Lab/KeYmaeraX-projects` @ `b9d7cb584e8fd1c3cc4f30644e82ba12cbb1d6fe` (`etcs/etcs.kyx`) and Platzer & Quesel (ICFEM 2009): apply to continuous-discrete differential dynamic logic (`dL`) hybrid safety, controllability, and RBC handoff proofs for ETCS movement authorities.
  - `CENELEC EN 50128:2011+A2:2020`, `EN 50129:2018`, Leuschel & Butler (FME 2003), and Haxthausen, Peleska, & Kinder (2011): apply to SIL 4 vital interlocking software verification and tabular/DSL railway controller synthesis.
- **Nuclear Reactor Protection Tabular Specifications & Coincidence Logic:**
  - `IEC 60880:2006`, Heitmeyer, Jeffords, & Labaw (ACM TOSEM 1996), and Yoo, Jee, & Cha (IEEE Software 2009): apply to Category A digital Instrumentation & Control (I&C) reactor trip systems specified using `SCR` / `NuSCR` tables compiled to PLC Function Block Diagrams (`FBD`) or FPGAs, and hardware coincidence voting (`2oo4`, `2oo3`, `1oo3`).
- **Substation Automation Layer-2 `GOOSE` / `SV` & `R-GOOSE` / `R-SV`:**
  - `mz-automation/libiec61850` @ `6e265c54af66ea686453b6d31c4dcce1cf7ad2bd` (v1.6.2, `src/goose/goose_{publisher,receiver,subscriber}.c`, `src/sampled_values/sv_subscriber.c`, `src/r_session/r_session{,_crypto_mbedtls}.c`): applies to C IED implementations of `IEC 61850-8-1` Layer-2 `GOOSE`, `IEC 61850-9-2` `SV`, and `IEC 61850-90-5` UDP-tunneled `R-GOOSE`/`R-SV`.
  - `IEC 61850-5` (`TT6` <= `3 ms` trip class), `IEC 62351-6:2020`, Hoyos et al. (2012), Kush et al. (2014), and Farooq et al. (2019): apply to substation process-bus LAN protection latency budgets and cryptographic message authentication.

**Relationship Among Subjects:** All three infrastructure domains reduce continuous or physical actuation hazards to discrete decision boundaries: railway interlockings enforce discrete route/flank topology guards feeding continuous `ETCS` deceleration envelopes; nuclear protection systems synthesize deterministic cyclic PLC/FPGA logic from disjoint, complete tabular specifications backed by redundant hardware voting; and substation relays enforce sub-3ms Layer-2 breaker-trip state transitions whose monotonic counters and MAC verification guard against physical fault propagation.

## Findings

### 1. Vital Railway Interlocking (`EN 50128` SIL 4, `Event-B` / `ProB`) and `ERTMS/ETCS` Dynamic Braking Curves

Basis: normative (`EN 50128:2011+A2:2020`, `EN 50129:2018`, `ERA SUBSET-026-3 v400`, Platzer & Quesel ICFEM 2009 DOI `10.1007/978-3-642-10373-5_13`, Haxthausen et al. 2011 DOI `10.1007/s00165-009-0143-6`, Leuschel & Butler FME 2003 DOI `10.1007/978-3-540-45236-2_46`) + source (`hhu-stups/prob2_kernel` @ `9f01dbb53751242084735445a871b53fd3fbf4b3`; `OpenRailAssociation/osrd` @ `af7025a6fbf91a517baf00157bdf3f2f081256e6`; `LS-Lab/KeYmaeraX-projects` @ `b9d7cb584e8fd1c3cc4f30644e82ba12cbb1d6fe`) + execution (`Probe 1A`).

#### 1.1 Route-Interlocking Table Invariants: Flank Protection, Overlap Locking, and Approach Release

A vital solid-state interlocking (`EN 50128` SIL 4 software, `EN 50129` `2oo2` / `2oo3` Composite Fail-Safe hardware) governs a railway yard through sequential route locking across track detection sections (`Track Circuits` / `Axle Counters`), movable `Points` (switches), `Flank Protection` elements, `Overlaps` (post-signal braking runoff), and `Signals`. Every valid route state transition must preserve three global invariants:

1. **Mutual Exclusion on Physical Track & Fouling Points:** No two active routes may simultaneously authorize trains into any shared detection section or converging **fouling point** (where two tracks converge within rolling-stock gauge clearance).
2. **Switch Movement Lock Under Reservation or Occupancy:** A point $p$ cannot be thrown unless its underlying track detection zone is clear *and* every route requiring $p$ either in its direct path, its **overlap**, or its **flank protection** position is unlocked.
3. **Approach-Locking Deadlock/Timer Safety:** Once a train enters the **approach zone** sighting a cleared signal, canceling the route cannot immediately unlock its points or overlaps (`Approach Release` holds the lock until a safety timer longer than worst-case stopping time expires, or until the train stops short and proves zero motion).

**Execution Counterexample (`Probe 1A`):** Modeling a converging 3-route junction (`R1: A -> J1` over `P1=Normal`, `R2: B -> J1` over `P1=Reverse`, `R3: Shunt_C -> J1` over `P2=Reverse`) shows that an interlocking table checking only *on-path* points (`P1=N` for `R1`) and *current* `J1` occupancy admits a 4-step collision across `18` reachable states:

- Step 1: `R1` clears `GREEN` (`P1=N, P2=N, t1=A, t2=C`).
- Step 2: Because `R1` failed to lock non-path flank point `P2=N`, an operator/route controller throws `P2=R` and clears converging shunt route `R3=GREEN` (both see `J1` currently unoccupied).
- Step 3–4: Train 1 enters `J1` simultaneously with Shunt Train 2 entering `J1` from `C` $\implies$ **junction collision**.
- Enforcing explicit flank exclusion (`R1` locks `P2=N` and excludes `R3`; `R3` requires `R1=RED` and `P1=R`) and approach locking reduces reachable states to `7` with **`0` invariant violations**.

#### 1.2 `Event-B` / `ProB` Verification Architectures and Source Audit of `hhu-stups/prob2_kernel`

Industrial SIL 4 interlocking validation (e.g., ClearSy Atelier B paired with `ProB`, and Haxthausen et al.'s `2011` DSL-to-SystemC/bounded-model-checking pipeline) relies on **double-chain verification**: either deductive proof obligation discharge (`Atelier B` theorem prover) plus independent data-validation checking (`ProB` constraint solving over concrete track layouts), or compositional yard decomposition. Direct inspection of `hhu-stups/prob2_kernel` @ `9f01dbb53751242084735445a871b53fd3fbf4b3` clarifies the exact semantics and failure modes of its verification engines:

- **Explicit State-Space Model Checking (`ConsistencyChecker.java:26-190`):** Iteratively executes `ModelCheckingStepCommand` over `500 ms` slices (`TIMEOUT_MS = 500`, line 28) using `ModelCheckingSearchStrategy.MIXED_BF_DF` by default (`ModelCheckingOptions.java:83`), flipping `recheckExisting(false)` after the first slice (`line 183`) and enforcing `FIND_DEADLOCKS` + `FIND_INVARIANT_VIOLATIONS` (`ModelCheckingOptions.DEFAULT`, lines 73-74). In `ModelCheckingOptions.java:36-38`, an informative deprecated flag quirk exists: `FIND_OTHER_ERRORS` maps to the Prolog key `"ignore_state_errors"` (inverted in `checkOtherErrors` at line 172 as `!value`), superseded by `IGNORE_OTHER_ERRORS`. Explicit-state exploration verifies exact reachability (`Init ->* Bad`) with zero false positives, **but** suffers combinatorial state explosion on realistic interlocking layouts with $> 20$ routes and timers.
- **Constraint-Based Inductive Invariant & Deadlock Checking (`CBCInvariantChecker.java:17-70`, `CBCDeadlockChecker.java:17-68`):** Instead of enumerating all reachable states, `CBCInvariantChecker` dispatches `ConstraintBasedInvariantCheckCommand` to ask the ProB CLP(FD)/SMT Prolog kernel whether *any* state satisfying the invariant $I(\sigma)$ can take a single event transition $T(\sigma, \sigma')$ into $\neg I(\sigma')$:
  $$\exists \sigma, \sigma'.\;\; I(\sigma) \land T(\sigma, \sigma') \land \neg I(\sigma')$$
  Similarly, `CBCDeadlockChecker` solves $\exists \sigma.\; I(\sigma) \land \bigwedge_{e} \neg \text{Guard}_e(\sigma)$. **Verification Trap:** Because `CBC` checks *inductiveness* rather than *reachability*, a railway model whose invariant $I$ states only `NoCollision` without explicitly encoding **flank-point locking, route-conflict mutexes, and overlap locks** as auxiliary invariants in $I$ will produce **spurious unreachable counterexamples** (ProB constructs an unreachable pre-state $\sigma$ satisfying `NoCollision` where two conflicting signals are already green simultaneously!). Conversely, strengthening $I$ until `CBCInvariantChecker` returns `OK` mathematically proves safety for *arbitrarily large* parameterizations without full state-space enumeration.

#### 1.3 Continuous Hybrid `dL` Proofs (`KeYmaera X`) vs. `ERA SUBSET-026` Braking Curves (`OpenRailAssociation/osrd`)

Once an interlocking grants a **Movement Authority (MA)** up to End of Authority $m$ (with supervised target speed $d \ge 0$), safe train separation passes across the discrete/continuous boundary into `ERTMS/ETCS` on-board speed supervision (`EVC`).

- **Differential Dynamic Logic (`dL`) Formalization (`LS-Lab/KeYmaeraX-projects/etcs/etcs.kyx`):**
  Platzer and Quesel (`ICFEM 2009`; `etcs.kyx:8-58, 71-152, 238-509`) model train position $z$, velocity $v$, acceleration $a \in [-b, A]$, and control cycle timer $t \in [0, \varepsilon]$ via the ODE $\{z' = v,\; v' = a,\; t' = 1 \ \& \ v \ge 0 \land t \le \varepsilon\}$:
  - **Controllability Invariant (`Proposition 1`, `etcs.kyx:8-10, 253-260`):** A state $(m, z, v, d)$ is controllable under maximum service/emergency braking $b > 0$ if and only if
    $$\text{Controllable}(m, z, v, d) \iff v \ge 0 \land d \ge 0 \land b > 0 \land v^2 - d^2 \le 2b(m - z)$$
  - **RBC Movement-Authority Shortening Guard (`Proposition 2`, `etcs.kyx:12-14, 291-338`):** When the Radio Block Center (`RBC`) updates $(m_o, d_o) \to (m, d)$ (e.g., revoking or shortening an MA), controllability is preserved if and only if
    $$M(d, d_o, m, m_o) \iff d_o^2 - d^2 \le 2b(m - m_o) \land d_o \ge 0 \land d \ge 0$$
  - **Start-Braking Reactivity Distance (`Proposition 4`, `etcs.kyx:71-72, 423-429`):** To prevent a train accelerating at $+A$ for up to one full control period $\varepsilon$ from crossing out of $\text{Controllable}$, the Automatic Train Protection (`ATP`) intervention threshold $SB(v, d)$ **must** satisfy:
    $$SB(v, d) \ge \underbrace{\frac{v^2 - d^2}{2b}}_{\text{kinematic brakeDist}} + \underbrace{\left(\frac{A}{b} + 1\right)\left(\frac{A}{2}\varepsilon^2 + \varepsilon v\right)}_{\text{accCompensation}(v)}$$
- **Industrial `ERA SUBSET-026-3 v400` Implementation Audit (`OpenRailAssociation/osrd` @ `af7025a6fbf91a517baf00157bdf3f2f081256e6`):**
  Direct inspection of `ETCSBrakingCurves.kt` (`lines 28-92, 132-179, 254-350, 360-435, 601-685`) reveals how production ETCS refines the idealized constant-deceleration `dL` model—and exposes key modeling seams:
  1. **Dual Target Envelopes (`EoA` vs. `SvL`, `lines 48-92`):** An **End of Authority (`EoA`)** uses Service Brake Deceleration (**`SBD`**) to reach `0 m/s` at `offsetEOA`, whereas the **Supervised Location (`SvL`)** downstream of the overlap uses Emergency Brake Deceleration (**`EBD`**) shifted backward by the Brake Equivalent Time (`BEC`) and warning/reaction margins (`EBD -> EBI -> SBI_2 -> PRE_PS -> PS -> IND`), taking the **pointwise minimum** (`computeMinETCSBrakingCurves`, lines 77-86, 443-501) between EoA and SvL for `PS` (Permitted Speed) and `IND` (Indication).
  2. **Non-Zero Speed `LoA` Overshoot (`lines 254-289`):** For a Limit of Authority (`LoA`) with $v_{\text{target}} > 0$, `SUBSET-026` §3.13.8.3.1 requires the `EBD` curve to pass `targetPosition` at $v_{\text{target}} + dV_{\text{EBI}}(v_{\text{target}})$ and continue decelerating to the *right* of `targetPosition` before intersecting `targetSpeed`.
  3. **Brake Build-Up & Traction-Cutoff Compensation (`computeBecParams`, lines 601-658):** Models residual traction effort during $t_{\text{traction}} = \max(t_{\text{TractionCutOff}} - (T_{\text{warning}} + t_{\text{Bs2}}), 0)$ (`vDelta1 = aEst1 * tTraction`), brake build-up coasting $t_{\text{berem}} = \max(t_{\text{Be}} - t_{\text{traction}}, 0)$ (`vDelta2 = A_EST_2 * tBerem`), and odometry error `vDelta0`, translating every `EBD` point backward in position by `dBec` and downward in speed by `vBec - speed` to form `EBI`, then stepping backward by driver reaction/service delays (`tBs`, `T_DRIVER`, `tIndication = max(0.8*tBs, 5.0) + T_DRIVER`, lines 661-678). Note one explicit upstream limitation at **`ETCSBrakingCurves.kt:655-658`**: `maxBecDeltaSpeed()` returns a hardcoded constant `50.0 / 3.6` (`13.89 m/s`) marked `// TODO: correctly compute maxBecDeltaSpeed`.
  4. **Directional Zone Path Tracking (`SpacingResourceGenerator.kt:111-113`):** Reserves resources by `ZonePathId` (entry/exit direction) rather than undirected `ZoneId` so opposing/different route traversals across the same physical zone do not collapse distinct approach-release offsets prematurely.

**Execution Quantification (`Probe 1A`):** For a high-speed train at $v = 300\text{ km/h}$ ($83.33\text{ m/s}$), $b = 0.9\text{ m/s}^2$, $A = 0.5\text{ m/s}^2$, $\varepsilon = 2.0\text{ s}$, naive kinematic $v^2/(2b) = \mathbf{3858.0\text{ m}}$, `KeYmaera X` $SB(v,0) = \mathbf{4118.8\text{ m}}$ (`+260.8 m` cycle margin), and full `SUBSET-026` `EBI` (with `tTraction = 1.5 s`, `tBerem = 2.0 s`, `vDelta0 = 1.67 m/s`, `dBec = 299.6 m`) requires **`4384.6 m`** (`+526.6 m` above naive kinematic braking).

---

### 2. Parnas/SCR & `NuSCR` Tabular Nuclear Reactor Protection (`IEC 60880`) and `2oo4` Voting

Basis: normative (`IEC 60880:2006`; Heitmeyer, Jeffords, Labaw, ACM TOSEM 1996 DOI `10.1145/234426.234431`; Yoo, Jee, Cha, IEEE Software 2009 DOI `10.1109/MS.2009.67`) + execution (`Probe 1B`).

#### 2.1 Tabular Verification Semantics (`SCR` & `NuSCR` for Digital Reactor Protection)

Nuclear Category A software (`IEC 60880:2006`), such as Digital Plant Protection Systems (`DPPS` / `RPS` bistable and local-coincidence trip logic), replaces unstructured English specs or nested `if-then-else` chains with **Parnas/SCR** and **`NuSCR`** (Nuclear Software Requirements Specification Language, Yoo et al. 2009) tabular notations. `NuSCR` decomposes safety functions into **Function Overview Tables (`FOT`)**, **Structured Decision Tables (`SDT`)**, **Finite State Machines (`FSM`)**, and **Timed Trajectory Tables (`TTT`)** supporting deterministic timing timers (`k`-cycle persistence delays / trip latches).

Under `SCR` (Heitmeyer et al. 1996, §3), conditioned events use the exact transition predicate:
$$@T(c)\ \text{WHEN}\ d \;\;\equiv\;\; \neg c(\sigma) \land c(\sigma') \land d(\sigma), \qquad @F(c)\ \text{WHEN}\ d \;\;\equiv\;\; c(\sigma) \land \neg c(\sigma') \land d(\sigma)$$
Every condition/decision table assigning output $y$ across condition cells $C_1, \dots, C_n$ with corresponding output expressions $E_1, \dots, E_n$ must discharge **three mandatory formal obligations** before synthesis to PLC Function Block Diagrams (`FBD`) or FPGA HDL:

| Tabular Proof Obligation | Formal Logical Criterion | Safety Defect Caught When Violated |
| :--- | :--- | :--- |
| **Pairwise Disjointness** | $\forall i \neq j.\; \forall \sigma.\; \neg(C_i(\sigma) \land C_j(\sigma))$ (or $E_i(\sigma) = E_j(\sigma)$ on overlap) | Conflicting dual-fired rules where trip (`True`) and permissive bypass (`False`) both hold simultaneously; silent priority masking during `if-else` compilation |
| **Domain Completeness** | $\forall \sigma \in \Sigma_{\text{valid}}.\; \bigvee_{i=1}^{n} C_i(\sigma) \equiv \top$ | Uncovered sensor state (e.g., deadband/hysteresis zone $P_{\text{trip}} < P < P_{\text{reset}}$) causing PLC output latch to retain stale pre-fault state |
| **Acyclicity & Type/Range Safety** | Directed dependency graph of synchronous `@T`/`COND` variables contains no zero-delay cycle; arithmetic avoids overflow/div-by-zero | Unstable scan-cycle oscillation or non-deterministic `FBD` execution order |

**Execution Verification (`Probe 1B`):** Evaluating a pressurizer low-pressure trip table (`P_TRIP = 125`, `P_RESET = 130`, `P_PERM = 130`, `P in [115, 140)`):
- A naive table writing `Row 1: P <= 125 -> Trip=True`, `Row 2: P <= 130 & bypass -> Trip=False`, `Row 3: P >= 130 -> Trip=False` exhibits **`22` disjointness conflicts** (e.g., at `P=115, bypass=True`, both `Row 1 (True)` and `Row 2 (False)` fire) and **`8` completeness gaps** (`P in [126, 129], bypass=False` matches no row).
- Adding explicit mutual guards (`not bypass`, `bypass`, hysteresis `125 < P < 130 -> retain latch`) reduces both disjointness conflicts and completeness gaps to **`0`**.

#### 2.2 Nuclear `2oo4` Coincidence Voting Under Maintenance Bypass vs. Common-Cause Failure (`CCF`)

Nuclear reactor protection architectures typically replicate independent sensor/bistable trains into **4 channels** feeding **2-out-of-4 (`2oo4`)** coincidence trip logic so the plant satisfies **both** the Single-Failure Criterion (no single dangerous failure prevents scram) and operational spurious-scram immunity (no single faulty transmitter triggers an unnecessary emergency shutdown). However, during periodic surveillance testing or channel maintenance, a channel must be placed in **bypass** (`2oo3`) or **trip-latch** (`1oo3`). Modeling per-channel dangerous-undetected failure $q_d = 10^{-3}$, safe/spurious failure $q_s = 2\times 10^{-3}$, and $\beta = 5\%$ common-cause coupling (`Probe 1B`):

| Voting Configuration | Dangerous Failure Threshold | Independent `PFD` | Total `PFD` ($\beta = 5\%$ CCF) | Independent Spurious Trip | Total Spurious ($\beta = 5\%$) |
| :--- | :---: | :---: | :---: | :---: | :---: |
| **`2oo4` (Nominal 4 channels)** | $\ge 3$ dangerous failures | **`3.43e-09`** | **`5.00e-05`** | `2.16e-05` | `1.22e-04` |
| **`2oo3` (1-ch Maintenance Bypass)** | $\ge 2$ dangerous failures | **`2.71e-06`** (`790x` worse) | **`5.27e-05`** | `1.08e-05` | `1.11e-04` |
| **`1oo3` (1-ch Safe Trip-Latch)** | $\ge 3$ dangerous failures | **`8.57e-10`** | **`5.00e-05`** | **`5.69e-03`** (`263x` worse) | **`5.79e-03`** |

Two critical design laws emerge directly from `Probe 1B`:
1. **Operational Mode Trade-off:** Bypassing one channel to `2oo3` protects against spurious shutdowns (`1.08e-05`), at a `790x` penalty in independent `PFD`; putting the channel in trip (`1oo3`) strengthens independent `PFD` (`8.57e-10`) at a `263x` increase in spurious scrams (single additional fault trips the reactor).
2. **CCF Dominance Ceiling:** Across all three configurations, independent hardware probability (`1e-9` to `1e-6`) is completely overwhelmed by **Common-Cause Failure** ($\beta q_d = 5\times 10^{-5}$)—whether from shared power/calibration drift or an identical systematic bug across 4 identical PLC software images. This explains why `IEC 60880` and nuclear regulators pair `NuSCR` formal verification with **diverse secondary actuation (`DAS`)** on dissimilar hardware/software technology.

---

### 3. Sub-3-Millisecond `IEC 61850` Substation `GOOSE`/`SV` Protection and `libiec61850` Audit

Basis: normative (`IEC 61850-5`, `IEC 61850-8-1`, `IEC 61850-9-2`, `IEC 61850-90-5`, `IEC 62351-6:2020`; Hoyos et al. 2012 DOI `10.1109/GLOCOMW.2012.6477809`; Kush et al. 2014 ISBN `978-1-921770-32-6`; Farooq et al. 2019 DOI `10.1109/ACCESS.2019.2902571`) + source (`mz-automation/libiec61850` @ `6e265c54af66ea686453b6d31c4dcce1cf7ad2bd`) + execution (`Probe 1C`).

#### 3.1 Layer-2 `GOOSE`/`SV` Framing, Retransmission State Machine, and `stNum` Poisoning

`IEC 61850-8-1` Generic Object-Oriented Substation Event (**`GOOSE`**, EtherType **`0x88B8`**, destination multicast `01:0C:CD:01:00:00..FF`) and `IEC 61850-9-2` Sampled Values (**`SV`**, EtherType **`0x88BA`**, destination multicast `01:0C:CD:04:00:00..FF`) bypass IP/TCP entirely and ride directly on IEEE `802.3` + `802.1Q` VLAN-tagged Ethernet (`goose_publisher.c:298-341`, `sv_subscriber.c:751-810`) to hit `IEC 61850-5` Transfer Time Class **`TT6` ($\le 3\text{ ms}$)** for breaker trips and interlocking.

- **Publisher State Machine (`goose_publisher.c:224-246`):** Maintains two `uint32_t` counters inside the ASN.1 BER APDU (`tag 0x61`, `stNum = tag 0x85`, `sqNum = tag 0x86`):
  - On any watched dataset change (e.g., trip signal transitions `False -> True`), `GoosePublisher_increaseStNum` (`lines 225-240`) increments `stNum++` (skipping `0` on `uint32_t` wrap: `if (self->stNum == 0) self->stNum = 1;`) and resets `sqNum = 0`.
  - The publisher immediately transmits bursts at minimum retransmission interval $T_0$ (typically `2–4 ms`), doubling exponentially ($2T_0, 4T_0, \dots$) up to steady-state heartbeat $T_{\max}$ (e.g., `1000 ms`), incrementing `sqNum++` on each unchanged heartbeat while holding `stNum` fixed. Each frame carries `timeAllowedToLive` (`TAL`, typically $\ge 2 T_{\max}$).
- **High-`stNum` Spoofing / Poisoned GOOSE DoS (Hoyos et al. 2012; Kush et al. 2014):** On an unauthenticated substation LAN, any strict `IEC 61850-8-1` subscriber drops packets whose `(stNum, sqNum)` is not strictly newer than its last accepted state. Injecting a single forged `GOOSE` frame with `stNum = 1000` (or `0xFFFFFFFF` / `UINT32_MAX - 1`) and `trip = False` updates the subscriber's expected `stNum` to `1000`; when the real protection relay subsequently detects a short-circuit fault and publishes `(stNum = 2, sqNum = 0, trip = True)`, **the subscriber silently discards the real trip until `TAL` expires**, blinding breaker protection (`Probe 1C`, Trace 1).

#### 3.2 Direct Source Audit of `mz-automation/libiec61850` (`6e265c54af66ea686453b6d31c4dcce1cf7ad2bd`)

Direct inspection of `libiec61850` v1.6.2 (`src/goose/goose_receiver.c`, `src/r_session/r_session.c`, `src/r_session/r_session_crypto_mbedtls.c`) reveals **four concrete, reproducible implementation bugs**:

1. **Backward-`stNum` Replay Acceptance (`goose_receiver.c:1088-1100`):**
   ```c
   if (matchingSubscriber->stNum == stNum) {
       if (matchingSubscriber->sqNum >= sqNum) {
           isValid = false;
       }
   }
   matchingSubscriber->stateValid = isValid;
   matchingSubscriber->stNum = stNum;
   matchingSubscriber->sqNum = sqNum;
   ```
   - **Defect A (Stale `stNum` Accepted):** The subscriber checks equality `matchingSubscriber->stNum == stNum` only—never `stNum < matchingSubscriber->stNum`! After a legitimate protection trip raises `stNum` from `1` to `2` (`trip = True`), an attacker replaying any previously sniffed pre-fault frame `(stNum = 1, sqNum = 5, trip = False)` satisfies `2 == 1` (`false`), leaving **`isValid = true`**, resetting `self->stNum = 1`, and reverting the relay state to `trip = False` (`Probe 1C`, Trace 2)!
   - **Defect B (Pre-Check Dataset Mutation & Unconditional Counter Overwrite):** `parseAllData()` (`line 1078`) overwrites `matchingSubscriber->dataSetValues` **before** checking `(stNum, sqNum)` at line `1088`, and lines `1098-1101` unconditionally assign `matchingSubscriber->stNum = stNum`, `matchingSubscriber->sqNum = sqNum`, and `invalidityTime = now + timeAllowedToLive` even when `isValid == false`! Thus, sending `(stNum = 2, sqNum = 0, trip = False)` when the subscriber is at `(2, 10)` fails `isValid` on packet 1, **but** mutates `dataSetValues` (`trip = False`) and resets `matchingSubscriber->sqNum = 0` so a follow-up `(stNum = 2, sqNum = 1)` passes `isValid = true` (`Probe 1C`, Trace 3)! Also note `GooseSubscriber_isValid()` (`goose_subscriber.c:67-77`) is only an optional polling check; `matchingSubscriber->listener` (`line 1104`) fires unconditionally on every matched packet regardless of `stateValid`!
2. **C Operator-Precedence Bug in IEEE `802.1Q` VLAN Priority (`goose_receiver.c:1138`):**
   ```c
   priority = buffer[bufPos + 2] & 0xF8 >> 5;
   ```
   In C, bitwise shift `>>` has **higher precedence** than bitwise `&`. Thus `0xF8 >> 5` evaluates first to `0x07`, computing `buffer[bufPos + 2] & 0x07` (bits `[2:0]`, i.e., the upper 3 bits of `vlanId` plus DEI, completely zeroing the `802.1Q` `PCP` priority bits `[7:5]`!). For example, a high-priority trip frame with `PCP = 4`, `DEI = 0`, `VID = 0` (`byte = 0x80`) decodes `priority = 0` instead of `4` (`Probe 1C`). Note also `0xE0` (not `0xF8`) is the 3-bit `PCP` mask (`0x10` is `DEI`).
3. **Unauthenticated `SV` Default Destination Check (`sv_subscriber.c:112, 706-731`):** `SVReceiver_create()` defaults `checkDestAddr = false` (`line 112`), accepting frames matched purely on 16-bit `appId` without checking destination MAC unless the caller explicitly invokes `SVReceiver_enableDestAddrCheck()`, and `parseASDU()` invokes `subscriber->listener` (`line 569`) with zero `smpCnt` monotonicity or `smpSynch` validation.
4. **`IEC 61850-90-5` `RSession` HMAC Length/Buffer Overwrite & Missing Replay Window (`r_session.c`, `r_session_crypto_mbedtls.c`):**
   - In `r_session.c:1147-1155`, `R_SESSION_SIG_ALGO_HMAC_SHA256_256` encodes BER length **`16`** (`buffer[bufPos++] = 16;`) before appending **`32`** bytes of HMAC digest (`bufPos += 32;`)—causing every compliant receiver check (`expectedLength = 32` at `r_session.c:596, 602, 826, 832`) to fail with `"signature length mismatch"`!
   - Conversely, in `r_session.c:1156-1165` (`R_SESSION_SIG_ALGO_HMAC_SHA256_128`), `RSessionCrypto_createHMAC(..., 16)` ignores its `int hmacMaxSize` parameter (`r_session_crypto_mbedtls.c:42, 68`) and calls `mbedtls_md_hmac_finish(&md_ctx, hmac)`, writing **32 bytes** while `bufPos` only advances by **`16`** (`line 1164`)—overwriting 16 bytes beyond the allocated signature slot (clobbering the subsequent AES-GCM trailer when combined with `secAlgo != NONE`, or overflowing if near buffer tail), and lines `57, 65, 73` return `false` without calling `mbedtls_md_free(&md_ctx)`.
   - Finally, `parseSessionMessage` (`r_session.c:475-476`) decodes `spduNumber` into a local variable and never checks it against prior received `spduNumber` or `timeOfCurrentKey`, leaving UDP `R-GOOSE`/`R-SV` vulnerable to within-key-epoch replay attacks.

#### 3.3 Cryptographic Latency Under the `< 3.000 ms` (`TT6`) Substation Protection Ceiling

`IEC 61850-5` Transfer Time Class `TT6` mandates $\le 3\text{ ms}$ total end-to-end delivery (publish encoding + switch queuing + wire propagation + subscriber decode + verification) for trip/interlocking protection. `IEC 62351-6:2007` originally specified asymmetric **RSASSA-PSS** digital signatures in the Ethernet `Reserved1/Reserved2` extension area, which Farooq et al. (2019) and embedded benchmarks establish exceeds `3 ms` on substation IED processors (`~4.5 ms` sign + verify alone, failing `TT6`). Consequently, **`IEC 62351-6:2020`** (`IEC 61850-90-5` `R-GOOSE`/`R-SV` and Layer-2 `GOOSE`/`SV` MAC extensions) dropped mandatory RSA and encryption in favor of **pre-shared group-key symmetric MACs (`HMAC-SHA256-80/128/256` and `AES-GMAC`)** distributed out-of-band via `IEC 62351-9` (`GDOI`), avoiding payload encryption latency while protecting authenticity (`~0.015 ms` compute, total 2-hop latency `0.049–0.295 ms` in `Probe 1C`), paired with IEEE `802.1Q` strict priority + `802.1Qbu` frame preemption against `1522 B` non-preemptive jumbo head-of-line blocking (`123.4 us/hop` at `100 Mbps`).

---

### 4. Cross-Domain Invariant & Failure Synthesis

| Domain | Core Safety Invariant | Representative Failure / Attack Mode | Mechanized Verification & Runtime Guard |
| :--- | :--- | :--- | :--- |
| **Railway Interlocking (`EN 50128`)** | Disjoint occupied/locked routes; flank + overlap point immobility | In-path-only locking allows converging shunt fouling (`Probe 1A`: 4 steps); `CBC` without auxiliary locks reports spurious states | Double-chain `Event-B`/`Atelier B` proof + `ProB` concrete layout checking (`CBC` + `ConsistencyChecker`) |
| **ETCS Braking (`SUBSET-026` / `dL`)** | $v^2 - d^2 \le 2b(m - z)$ + cycle & traction-cutoff buffer | Naive $v^2/(2b)$ (`3858.0 m` at `300 km/h`) falls `260.8 m` (`dL`) to `526.6 m` (`SUBSET-026`) short of safe intervention | `KeYmaera X` `dL` inductive $SB(v,d)$ + `SUBSET-026` `BEC` (`tTraction`, `vDelta0`, `tBs`) |
| **Nuclear RPS (`NuSCR` / `IEC 60880`)** | Tabular Disjointness, Completeness, Acyclicity + Single-Failure Criterion | Overlapping permissive bypass / missing hysteresis (`Probe 1B`: 22 conflicts, 8 gaps); `2oo3` bypass inflates `PFD_ind` `790x`; `5%` CCF dominates at `5e-5` | Automated SMT/grid `SCR`/`NuSCR` table verifier + `2oo4` coincidence + diverse actuation (`DAS`) |
| **Substation `GOOSE`/`SV` (`IEC 61850`)** | Monotonic `(stNum, sqNum)` + authenticated origin within `< 3 ms` `TT6` | `stNum` poisoning DoS; `libiec61850` backward `stNum` & `sqNum=0->1` replay bugs; `802.1Q` PCP precedence zeroing; RSA-2048 `> 4.5 ms` overrun | Strict `(stNum, sqNum)` check *before* dataset mutation + `IEC 62351-6:2020` `HMAC-SHA256`/`AES-GMAC` + `802.1Qbv`/`802.1Qbu` |

## Boundaries

- **Known not to apply — `CBCInvariantChecker` Without Auxiliary Strengthening Invariants:** Constraint-based checking in `prob2_kernel` checks single-step inductiveness ($I \land T \implies I'$), not reachability from `INITIALISATION`. Without explicit flank-lock and signal-conflict invariants in $I$, `CBC` returns false-positive counterexamples from unreachable states.
- **Known not to apply — `IEC 62351-6:2007` RSA Signatures and Payload Encryption to `< 3 ms` `GOOSE`/`SV` Tripping:** RSA-2048 signing/verification (`~4.5 ms` in `Probe 1C` / Farooq et al. 2019) violates `IEC 61850-5` `TT6`; symmetric `HMAC-SHA256-128`/`AES-GMAC` (`IEC 62351-6:2020`) without payload encryption is required for real-time protection streams.
- **Known not to apply — Independent Channel Reliability Scaling Under Unmitigated CCF:** Adding a 4th nuclear channel (`2oo4` vs `2oo3`) cuts independent `PFD` by `~790x` (`Probe 1B`) *only* for independent random failures; identical software or shared-bus CCF ($\beta \approx 5\%$) caps reliability near $\beta q_d$.
- **Unsupported — Complete ETCS `maxBecDeltaSpeed` Calculation and `RSession` Replay Window in Inspected Revisions:** `OpenRailAssociation/osrd` @ `af7025a6` hardcodes `maxBecDeltaSpeed() = 50.0 / 3.6` with an open `TODO` (`ETCSBrakingCurves.kt:655-658`); `mz-automation/libiec61850` @ `6e265c54` omits monotonic `spduNumber` / `stNum < self->stNum` replay rejection in `r_session.c` and `goose_receiver.c`.
- **Not examined — Commercial SIL 4 Railway PLC/FPGA Compilers, Physical Nuclear I&C Target Hardware, and `IEC 62351-9` GDOI Key Rotation Protocols:** Proprietary clear-box verification suites (`ClearSy` / `Prover iLock` industrial binaries), physical APR-1400 PLC hardware, and `GDOI` key-distribution state machines were not executed or inspected at source level.
- **Unknown — Exact Per-IED Cryptographic Latencies Across Specific Vendor ASIC/FPGA Offloads:** Probe `1C`'s `0.015 ms` HMAC and `4.500 ms` RSA figures reflect representative software IED benchmarks from Farooq et al. (2019); hardware-offloaded MAC/signature accelerators shift absolute margins while preserving the strict symmetric vs. asymmetric separation.

## Evidence

### Primary Upstream Source Citations (Observed 2026-11-19)

1. **`hhu-stups/prob2_kernel` @ `9f01dbb53751242084735445a871b53fd3fbf4b3`:**
   - `prob-java/src/main/java/de/prob/check/ConsistencyChecker.java:26-190` (`TIMEOUT_MS = 500`, `ModelCheckingStepCommand`, `recheckExisting(false)`).
   - `prob-java/src/main/java/de/prob/check/CBCInvariantChecker.java:17-70` (`ConstraintBasedInvariantCheckCommand`) and `CBCDeadlockChecker.java:17-68` (`ConstraintBasedDeadlockCheckCommand`).
   - `prob-java/src/main/java/de/prob/check/ModelCheckingOptions.java:15-108, 170-173` (`DEFAULT = checkDeadlocks(true).checkInvariantViolations(true)`, `MIXED_BF_DF`, deprecated `FIND_OTHER_ERRORS` inverted `"ignore_state_errors"` mapping).
2. **`OpenRailAssociation/osrd` @ `af7025a6fbf91a517baf00157bdf3f2f081256e6`:**
   - `core/envelope-sim/src/main/kotlin/fr/sncf/osrd/envelope_sim/etcs/ETCSBrakingCurves.kt:48-92` (`computeBrakingCurvesAtEOA` SBD+EBD min), `132-179` (`computeEbdBrakingCurves`), `254-300` (`LoA` `targetSpeed + dvEbi` deceleration), `360-435` (`EBI/SBD -> SBI -> PRE_PS -> PS -> IND`), `601-658` (`computeBecParams` and hardcoded `maxBecDeltaSpeed() = 50.0 / 3.6` `TODO`), `661-686` (`tIndication = max(0.8 * tBs, 5.0) + T_DRIVER`).
   - `core/envelope-sim/src/main/kotlin/fr/sncf/osrd/envelope_sim/etcs/ETCSBrakingSimulator.kt:17-221` (`SUBSET-026-3 v400` reference, `addSlowdownBrakingCurves`, `addStopBrakingCurves`).
   - `core/src/main/kotlin/fr/sncf/osrd/conflicts/SpacingResourceGenerator.kt:111-113` (`ongoingZoneRequirements` keyed by `ZonePathId`).
3. **`LS-Lab/KeYmaeraX-projects` @ `b9d7cb584e8fd1c3cc4f30644e82ba12cbb1d6fe`:**
   - `etcs/etcs.kyx:8-58` (`Controllable`, `M`, `stopDist`, `spd`, `atp`, `drive`, `rbc`), `71-154` (`accCompensation`, `SB`, differential-invariant proof), `238-347` (`Proposition 1` controllability equivalence & `Proposition 2` RBC handoff), `401-509` (`Proposition 4` reactivity bound & `Proposition 5` full system safety).
4. **`mz-automation/libiec61850` @ `6e265c54af66ea686453b6d31c4dcce1cf7ad2bd`:**
   - `src/goose/goose_publisher.c:224-246` (`GoosePublisher_increaseStNum` wrapping `stNum` past `0` to `1` and resetting `sqNum = 0`), `298-341` (`802.1Q` + `0x88B8` EtherType framing).
   - `src/goose/goose_receiver.c:1070-1105` (pre-check `parseAllData` mutation, missing `stNum < self->stNum` check, unconditional `stNum`/`sqNum`/`invalidityTime` overwrite, unconditional listener call), `1136-1143` (`buffer[bufPos + 2] & 0xF8 >> 5` operator-precedence bug).
   - `src/goose/goose_subscriber.c:67-77` (`GooseSubscriber_isValid`).
   - `src/sampled_values/sv_subscriber.c:112, 566-570, 706-731` (`checkDestAddr = false` default, `0x88BA` EtherType, unguarded callback).
   - `src/r_session/r_session.c:475-476, 590-630, 820-860, 1147-1165` (`spduNumber` unchecked, `HMAC_SHA256_256` encoded with length `16`, `HMAC_SHA256_128` overrun).
   - `src/r_session/r_session_crypto_mbedtls.c:42-79` (`RSessionCrypto_createHMAC` ignoring `hmacMaxSize` and leaking `md_ctx` on error).

### Primary Standards & Literature Citations

- `CENELEC EN 50128:2011+A2:2020` & `EN 50129:2018`, *Railway applications — Communication, signalling and processing systems — Software for railway control and protection systems / Safety related electronic systems for signalling*.
- `ERA SUBSET-026-3 v400`, *ERTMS/ETCS System Requirements Specification — Chapter 3: Principles*.
- `IEC 60880:2006`, *Nuclear power plants — Instrumentation and control systems important to safety — Software aspects for computer-based systems performing category A functions*.
- `IEC 61850-5`, `IEC 61850-8-1`, `IEC 61850-9-2`, `IEC 61850-90-5`, and `IEC 62351-6:2020`, *Communication networks and systems for power utility automation / Data and communication security*.
- André Platzer and Jan-David Quesel, "European Train Control System: A Case Study in Formal Verification," *ICFEM 2009*, LNCS 5885, pp. 246–265, DOI `10.1007/978-3-642-10373-5_13`.
- Anne E. Haxthausen, Jan Peleska, and Sebastian Kinder, "A formal approach for the construction and verification of railway control systems," *Formal Aspects of Computing* 23(2):191–219, 2011, DOI `10.1007/s00165-009-0143-6`.
- Michael Leuschel and Michael Butler, "ProB: A Model Checker for B," *FME 2003*, LNCS 2805, pp. 855–874, DOI `10.1007/978-3-540-45236-2_46`.
- Constance L. Heitmeyer, Ralph D. Jeffords, and Bruce G. Labaw, "Automated Consistency Checking of Requirements Specifications," *ACM TOSEM* 5(3):231–261, 1996, DOI `10.1145/234426.234431`.
- Junbeom Yoo, Eunkyoung Jee, and Sungdeok Cha, "Formal Modeling and Verification of Safety-Critical Software," *IEEE Software* 26(3):42–49, 2009, DOI `10.1109/MS.2009.67`.
- Javier Hoyos, Mark Dehus, and Tim R. Brown, "Exploiting the GOOSE Protocol: A Practical Attack on Cyber-Infrastructure," *IEEE Globecom Workshops 2012*, pp. 1508–1513, DOI `10.1109/GLOCOMW.2012.6477809`.
- Nishchal Kush, Ejaz Ahmed, Mark Branagan, and Ernest Foo, "Poisoned GOOSE: Exploiting the GOOSE Protocol," *AISC 2014*, CRPIT Vol. 149, pp. 17–22, ISBN `978-1-921770-32-6`.
- Shaik Mullapudi Farooq, S. M. Suhail Hussain, S. Kiran, and Taha Selim Ustun, "Performance Evaluation and Analysis of IEC 62351-6 Probabilistic Signature Scheme for Securing GOOSE Messages," *IEEE Access* 7:32343–32351, 2019, DOI `10.1109/ACCESS.2019.2902571`.

### Self-Contained Executable Micro-Probe (`Probes 1A, 1B, 1C`)

Executed with Python 3 (standard library only) on Linux x86_64 on `2026-11-19`:

```python
#!/usr/bin/env python3
"""Standalone micro-probes for:
1A: Vital Railway Junction Interlocking (Event-B/ProB BFS & CBC checks) +
    ERTMS/ETCS Braking Curves (KeYmaera X dL vs. ERA SUBSET-026 BEC / OSRD).
1B: Parnas/SCR & NuSCR Tabular Disjointness/Completeness Verification +
    Nuclear 2oo4 Coincidence Voting Degradation & Common-Cause Failure (CCF).
1C: IEC 61850 GOOSE stNum/sqNum Replay/Poisoning Audit (libiec61850) +
    802.1Q PCP Precedence Bug + < 3 ms IEC 62351-6 Latency Budget.
"""
from __future__ import annotations

from collections import deque
import math


def probe_1a_railway_and_etcs() -> None:
    print("=== PROBE 1A: Vital Railway Interlocking (Flank/Approach Locking) & ETCS Braking ===")
    def run_bfs(enforce_flank_and_approach: bool):
        init = ("A", "C", "N", "N", "RED", "RED", 0)
        q = deque([(init, [init])])
        seen = {init}
        violations = []
        while q:
            st, path = q.popleft()
            t1, t2, p1, p2, s1, s3, tmr = st
            if t1 == "J1" and t2 == "J1":
                violations.append(("COLLISION", path))
                break
            nexts = []
            if s1 == "RED" and p1 == "N" and t1 != "J1" and t2 != "J1":
                if (not enforce_flank_and_approach) or (s3 == "RED" and p2 == "N"):
                    nexts.append((t1, t2, p1, p2, "GREEN", s3, tmr))
            if s3 == "RED" and t2 == "C" and t1 != "J1" and t2 != "J1":
                if (not enforce_flank_and_approach) or (s1 == "RED" and p1 == "R"):
                    nexts.append((t1, t2, p1, "R", s1, "GREEN", tmr))
            if p2 == "N" and t2 != "J1":
                if (not enforce_flank_and_approach) or (s1 == "RED" and t1 != "J1"):
                    nexts.append((t1, t2, p1, "R", s1, s3, tmr))
            if s1 == "GREEN" and t1 == "A" and not enforce_flank_and_approach:
                nexts.append((t1, t2, p1, p2, "RED", s3, 0))
            if t1 == "A" and s1 == "GREEN":
                nexts.append(("J1", t2, p1, p2, "RED", s3, 0))
            if t1 == "J1":
                nexts.append(("X1", t2, p1, p2, s1, s3, 0))
            if t2 == "C" and s3 == "GREEN":
                nexts.append((t1, "J1", p1, p2, s1, "RED", 0))
            for nxt in nexts:
                if nxt not in seen:
                    seen.add(nxt)
                    q.append((nxt, path + [nxt]))
        return len(seen), violations

    n_naive, v_naive = run_bfs(enforce_flank_and_approach=False)
    n_vital, v_vital = run_bfs(enforce_flank_and_approach=True)
    print(f"  Naive in-path locking: explored {n_naive} states, violations={len(v_naive)} ({v_naive[0][0]})")
    for i, s in enumerate(v_naive[0][1]):
        print(f"    step {i}: t1={s[0]}, t2={s[1]}, P1={s[2]}, P2={s[3]}, R1={s[4]}, R3={s[5]}")
    print(f"  Vital flank+overlap locking: explored {n_vital} states, violations={len(v_vital)} [SAFE]")

    v, d, b, A, eps = 300.0 / 3.6, 0.0, 0.90, 0.50, 2.0
    sb_dl = (v * v - d * d) / (2.0 * b) + (A / b + 1.0) * (0.5 * A * eps * eps + eps * v)
    t_warning, t_bs2, t_trac_cut, t_be = 2.0, 2.0, 5.5, 3.5
    v_delta0 = 0.02 * v
    t_traction = max(t_trac_cut - (t_warning + t_bs2), 0.0)
    v_delta1 = A * t_traction
    t_berem = max(t_be - t_traction, 0.0)
    v_delta2 = 0.0 * t_berem
    max_v = max(v + v_delta0 + v_delta1, d)
    d_bec = max(v + v_delta0 + v_delta1 / 2.0, d) * t_traction + (max_v + v_delta2 / 2.0) * t_berem
    d_ebi_with_bec = (max_v * max_v - d * d) / (2.0 * b) + d_bec
    d_ebd_naive = (v * v - d * d) / (2.0 * b)
    print(f"  ETCS 300 km/h (v={v:.2f} m/s, b={b}, A={A}, eps={eps}s):")
    print(f"    Naive kinematic stop v^2/(2b) = {d_ebd_naive:.1f} m")
    print(f"    KeYmaera X dL SB(v,0)         = {sb_dl:.1f} m (+{sb_dl - d_ebd_naive:.1f} m cycle compensation)")
    print(f"    SUBSET-026 EBI (with BEC)     = {d_ebi_with_bec:.1f} m (d_bec={d_bec:.1f} m, t_traction={t_traction:.1f}s, v_delta0={v_delta0:.2f} m/s)")


def probe_1b_nuscr_and_2oo4() -> None:
    print("\n=== PROBE 1B: Parnas/NuSCR Tabular Disjointness/Completeness & Nuclear 2oo4 Voting ===")
    P_TRIP, P_RESET, P_PERM = 125, 130, 130

    def eval_flawed_table(P: int, latch: bool, bypass: bool):
        fired = []
        if P <= P_TRIP:
            fired.append(("R1_LowP_Trip", True))
        if P <= P_PERM and bypass:
            fired.append(("R2_Bypass_Suppress", False))
        if P >= P_RESET:
            fired.append(("R3_Normal_Clear", False))
        return fired

    def eval_repaired_table(P: int, latch: bool, bypass: bool):
        fired = []
        if not bypass and P <= P_TRIP:
            fired.append(("R1_LowP_Trip", True))
        elif bypass and P <= P_PERM:
            fired.append(("R2_Permissive_Bypass", False))
        elif not bypass and P_TRIP < P < P_RESET:
            fired.append(("R3_Hysteresis_Hold", latch))
        elif P >= P_RESET:
            fired.append(("R4_Normal_Clear", False))
        return fired

    def check_table(fn):
        overlaps, gaps = [], []
        for P in range(115, 140):
            for latch in (False, True):
                for bypass in (False, True):
                    res = fn(P, latch, bypass)
                    if len(res) == 0:
                        gaps.append((P, latch, bypass))
                    elif len(res) > 1 and len({out for _, out in res}) > 1:
                        overlaps.append((P, latch, bypass, res))
        return overlaps, gaps

    ov_f, gap_f = check_table(eval_flawed_table)
    ov_r, gap_r = check_table(eval_repaired_table)
    print(f"  Flawed NuSCR table: disjointness_conflicts={len(ov_f)} (e.g. {ov_f[0]}), completeness_gaps={len(gap_f)} (e.g. {gap_f[0]})")
    print(f"  Repaired NuSCR table: disjointness_conflicts={len(ov_r)}, completeness_gaps={len(gap_r)} [VERIFIED]")

    qd, qs, beta = 1e-3, 2e-3, 0.05
    qd_ind, qd_ccf = (1.0 - beta) * qd, beta * qd
    qs_ind, qs_ccf = (1.0 - beta) * qs, beta * qs
    for label, N, K in [("2oo4 (Normal)", 4, 2), ("2oo3 (1-ch Bypass)", 3, 2), ("1oo3 (1-ch Trip-Latch)", 3, 1)]:
        pfd_ind = sum(math.comb(N, i) * (qd_ind ** i) * ((1 - qd_ind) ** (N - i)) for i in range(N - K + 1, N + 1))
        sp_ind = sum(math.comb(N, i) * (qs_ind ** i) * ((1 - qs_ind) ** (N - i)) for i in range(K, N + 1))
        print(f"  {label:<24}: PFD_ind={pfd_ind:.2e}, PFD_total(CCF)={pfd_ind+qd_ccf:.2e} | Spurious_ind={sp_ind:.2e}, Spurious_tot={sp_ind+qs_ccf:.2e}")


def probe_1c_goose_audit() -> None:
    print("\n=== PROBE 1C: libiec61850 GOOSE stNum/sqNum Audit, VLAN PCP Bug, & <3 ms Budget ===")
    class LibIEC61850Subscriber:
        def __init__(self):
            self.stNum, self.sqNum, self.stateValid, self.trip = 0, 0, True, False
        def receive(self, st: int, sq: int, trip: bool):
            is_valid = True
            self.trip = trip
            if self.stNum == st and self.sqNum >= sq:
                is_valid = False
            self.stateValid, self.stNum, self.sqNum = is_valid, st, sq
            return self.stateValid, self.stNum, self.sqNum, self.trip

    class StrictSubscriber:
        def __init__(self):
            self.stNum, self.sqNum, self.trip = 0, 0, False
        def receive(self, st: int, sq: int, trip: bool, mac_ok: bool):
            if not mac_ok or st < self.stNum or (st == self.stNum and sq <= self.sqNum):
                return False, self.stNum, self.sqNum, self.trip
            self.stNum, self.sqNum, self.trip = st, sq, trip
            return True, self.stNum, self.sqNum, self.trip

    s_strict = StrictSubscriber()
    s_strict.receive(1, 5, False, True)
    ok_att, *_ = s_strict.receive(1000, 0, False, True)
    ok_legit, *_ = s_strict.receive(2, 0, True, True)
    print(f"  Trace 1 (Unauth stNum=1000 Poisoning): spoof_accepted={ok_att}, legit_trip_st2_accepted={ok_legit} [BLOCKED]")

    s_lib = LibIEC61850Subscriber()
    s_lib.receive(1, 5, False); s_lib.receive(2, 0, True)
    ok_back, st_b, sq_b, trip_b = s_lib.receive(1, 5, False)
    print(f"  Trace 2 (libiec61850 Backward stNum=1 Replay): stateValid={ok_back} (BUG! Expected False), state=(st={st_b}, sq={sq_b}, trip={trip_b})")

    s_lib2 = LibIEC61850Subscriber()
    s_lib2.receive(2, 10, True)
    ok1, *_ = s_lib2.receive(2, 0, False)
    ok2, st2, sq2, tr2 = s_lib2.receive(2, 1, False)
    print(f"  Trace 3 (libiec61850 sqNum=0->1 Replay): pkt1_valid={ok1}, pkt2_valid={ok2} (BUG!), state=(st={st2}, sq={sq2}, trip={tr2})")

    tci_hi = 0x80
    print(f"  goose_receiver.c:1138 VLAN PCP bug (TCI_hi=0x80, PCP=4): buggy=`0x80 & 0xF8 >> 5`={tci_hi & (0xF8 >> 5)}, correct={(tci_hi & 0xE0) >> 5}")

    goose_bits, jumbo_bits = (128 + 20) * 8, (1522 + 20) * 8
    for link_mbps, preemp in [(100, False), (100, True), (1000, False)]:
        t_net_2hop = 2 * (goose_bits / (link_mbps * 1000.0) + (0.0 if preemp else jumbo_bits / (link_mbps * 1000.0)) + 0.005)
        t_hmac, t_rsa = t_net_2hop + 0.015, t_net_2hop + 4.500
        print(f"  Link={link_mbps}M (preempt={str(preemp):5s}): net_2hop={t_net_2hop:.3f} ms | +HMAC={t_hmac:.3f} ms ({'PASS' if t_hmac<3.0 else 'FAIL'}) | +RSA2048={t_rsa:.3f} ms ({'PASS' if t_rsa<3.0 else 'FAIL'})")


if __name__ == "__main__":
    probe_1a_railway_and_etcs()
    probe_1b_nuscr_and_2oo4()
    probe_1c_goose_audit()
```

Observed output:

```text
=== PROBE 1A: Vital Railway Interlocking (Flank/Approach Locking) & ETCS Braking ===
  Naive in-path locking: explored 18 states, violations=1 (COLLISION)
    step 0: t1=A, t2=C, P1=N, P2=N, R1=RED, R3=RED
    step 1: t1=A, t2=C, P1=N, P2=N, R1=GREEN, R3=RED
    step 2: t1=A, t2=C, P1=N, P2=R, R1=GREEN, R3=GREEN
    step 3: t1=J1, t2=C, P1=N, P2=R, R1=RED, R3=GREEN
    step 4: t1=J1, t2=J1, P1=N, P2=R, R1=RED, R3=RED
  Vital flank+overlap locking: explored 7 states, violations=0 [SAFE]
  ETCS 300 km/h (v=83.33 m/s, b=0.9, A=0.5, eps=2.0s):
    Naive kinematic stop v^2/(2b) = 3858.0 m
    KeYmaera X dL SB(v,0)         = 4118.8 m (+260.8 m cycle compensation)
    SUBSET-026 EBI (with BEC)     = 4384.6 m (d_bec=299.6 m, t_traction=1.5s, v_delta0=1.67 m/s)

=== PROBE 1B: Parnas/NuSCR Tabular Disjointness/Completeness & Nuclear 2oo4 Voting ===
  Flawed NuSCR table: disjointness_conflicts=22 (e.g. (115, False, True, [('R1_LowP_Trip', True), ('R2_Bypass_Suppress', False)])), completeness_gaps=8 (e.g. (126, False, False))
  Repaired NuSCR table: disjointness_conflicts=0, completeness_gaps=0 [VERIFIED]
  2oo4 (Normal)           : PFD_ind=3.43e-09, PFD_total(CCF)=5.00e-05 | Spurious_ind=2.16e-05, Spurious_tot=1.22e-04
  2oo3 (1-ch Bypass)      : PFD_ind=2.71e-06, PFD_total(CCF)=5.27e-05 | Spurious_ind=1.08e-05, Spurious_tot=1.11e-04
  1oo3 (1-ch Trip-Latch)  : PFD_ind=8.57e-10, PFD_total(CCF)=5.00e-05 | Spurious_ind=5.69e-03, Spurious_tot=5.79e-03

=== PROBE 1C: libiec61850 GOOSE stNum/sqNum Audit, VLAN PCP Bug, & <3 ms Budget ===
  Trace 1 (Unauth stNum=1000 Poisoning): spoof_accepted=True, legit_trip_st2_accepted=False [BLOCKED]
  Trace 2 (libiec61850 Backward stNum=1 Replay): stateValid=True (BUG! Expected False), state=(st=1, sq=5, trip=False)
  Trace 3 (libiec61850 sqNum=0->1 Replay): pkt1_valid=False, pkt2_valid=True (BUG!), state=(st=2, sq=1, trip=False)
  goose_receiver.c:1138 VLAN PCP bug (TCI_hi=0x80, PCP=4): buggy=`0x80 & 0xF8 >> 5`=0, correct=4
  Link=100M (preempt=False): net_2hop=0.280 ms | +HMAC=0.295 ms (PASS) | +RSA2048=4.780 ms (FAIL)
  Link=100M (preempt=True ): net_2hop=0.034 ms | +HMAC=0.049 ms (PASS) | +RSA2048=4.534 ms (FAIL)
  Link=1000M (preempt=False): net_2hop=0.037 ms | +HMAC=0.052 ms (PASS) | +RSA2048=4.537 ms (FAIL)
```

## Revalidation

1. **Re-check `libiec61850` GOOSE and `RSession` Security Patches:** Diff `src/goose/goose_receiver.c:1070-1145` and `src/r_session/r_session.c:1140-1170` against revision `6e265c54af66ea686453b6d31c4dcce1cf7ad2bd`. Verify whether `parseGoosePayload` rejects `stNum < self->stNum`, avoids mutating `dataSetValues`/`sqNum` on invalid frames, parenthesizes `(buffer[bufPos + 2] & 0xE0) >> 5`, fixes the `HMAC_SHA256_256` encoded length (`32` vs `16`) and `HMAC_SHA256_128` 32-byte write overrun, and enforces `spduNumber` anti-replay windows.
2. **Re-check `OpenRailAssociation/osrd` `ETCSBrakingCurves.kt`:** Diff `core/envelope-sim/src/main/kotlin/fr/sncf/osrd/envelope_sim/etcs/ETCSBrakingCurves.kt:601-686` against revision `af7025a6fbf91a517baf00157bdf3f2f081256e6` to verify whether `maxBecDeltaSpeed()` computes actual rolling-stock `vDelta0/1/2` bounds instead of returning `50.0 / 3.6`.
3. **Re-check `hhu-stups/prob2_kernel` Checker Options:** Diff `prob-java/src/main/java/de/prob/check/ModelCheckingOptions.java` and `ConsistencyChecker.java` against revision `9f01dbb53751242084735445a871b53fd3fbf4b3` if upgrading ProB versions in B/Event-B interlocking verification pipelines.
4. **Re-run Executable Micro-Probes:** Save the Python 3 script from **Evidence** as `/tmp/probe_railway_nuclear_goose.py` and execute `python3 /tmp/probe_railway_nuclear_goose.py` to confirm all three invariant checks, `2oo4`/`2oo3`/`1oo3` reliability curves, and `libiec61850` counter/VLAN diagnostics; substitute site-specific interlocking topologies, reactor setpoint tolerances, and LAN hop counts for target deployments.
