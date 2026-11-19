# Physical Clock Synchronization, Bounded-Uncertainty Distributed Time (TrueTime/fbclock/HLC), PTP/Huygens/Byzantine Bounds, and Epistemic Temporal Type Systems

## Summary

Point-valued scalar timestamps (`u64`/`i64` nanoseconds since epoch) are a leaky abstraction for distributed consensus, real-time scheduling, and formal verification: physical oscillators drift, network paths exhibit unobservable one-way delay asymmetry, operating-system wall clocks step or smear across leap seconds, and virtual-machine live migrations inject sudden blackout jumps. Sound distributed and systems engineering requires treating time as an **epistemic bounded interval tagged with its timescale and locality domain**.

1. **Synchronization accuracy faces hard mathematical lower bounds under delay uncertainty and Byzantine faults.** Lundelius and Lynch (1984) proved that even with zero oscillator drift, $n$ clocks exchanging messages with delay in $[l, u]$ cannot guarantee synchronization precision tighter than $(u - l)(1 - 1/n)$. Under arbitrary (Byzantine) faults without cryptographic authentication, Dolev, Halpern, and Strong (1986) proved synchronization is **impossible for $n \le 3f$**, matching Lamport and Melliar-Smith's (1985) $n \ge 3f + 1$ threshold for Interactive Convergence (CNV). Probe 2B exhibits an explicit $n=3, f=1$ counterexample where CNV achieves zero convergence, while $n=4, f=1$ contracts toward the algebraic fixed-point spread $2\delta / 3$.
2. **Bounded-uncertainty interval APIs (Spanner TrueTime, Meta `fbclock`) buy strict serializability via commit-wait; Hybrid Logical Clocks (CockroachDB HLC) avoid commit-wait at the cost of read-uncertainty restarts and weaker out-of-band write ordering.**
   - **Spanner TrueTime** (`Corbett et al., OSDI 2012 / TOCS 2013`) exposes `TT.now() -> [earliest, latest]` with half-width $\varepsilon$ (typically 1–7 ms, growing as a 200 $\mu\text{s/s}$ sawtooth between 30 s master polls) and guarantees **external consistency (strict serializability)** by assigning commit timestamp $s_i = \text{TT.now().latest}$ and waiting until $\text{TT.after}(s_i)$ (up to $2\varepsilon$). Shortening the commit wait by even **1 ns** or breaching $|e| \le \varepsilon$ by **500 ns** immediately yields an external-consistency inversion (Probe 2A).
   - **Meta `fbclock`** (`facebook/time` @ `62fc415c...`) implements an open-source PTP/PHC-backed TrueTime-style Window of Uncertainty (WOU) over cache-line-aligned seqlocked shared memory (`alignas(64) atomic_uint64 seq`), computing $W(\Delta t) = \text{error\_bound\_ns} + \lfloor h \cdot \Delta t \rfloor$, failing closed past `FBCLOCK_MAX_EXTRAPOLATION_NS = 10s`, and explicitly warning in `fbclock.h` that collapsing `[earliest, latest]` to its midpoint discards correctness for event ordering.
   - **CockroachDB HLC** (`cockroachdb/cockroach` @ `d30c905f...`, implementing Kulkarni et al., OPODIS 2014) tracks causal happens-before without GPS/atomic hardware, enforces operator-promised skew bounds via `ClockTimestamp` capability typing, `UpdateAndCheckMaxOffset`, persisted `wallTimeUpperBound`, and `toleratedForwardClockJump = maxOffset / 2` self-termination, and defends overlapping reads via `ReadWithinUncertaintyIntervalError`—while still allowing real-time timestamp inversion for causally disconnected disjoint-key writes (Probe 2A).
3. **Sub-microsecond datacenter synchronization (IEEE 1588 PTP, 802.1Qbv TSN, Huygens) must defeat two-way path asymmetry and queuing jitter.** In `linuxptp` (`tsproc.c`), 4-timestamp PTP offset estimation $\hat{\theta} = (t_2 - t_1) - \frac{(t_2 - t_3) r + (t_4 - t_1)}{2}$ suffers an **unobservable systematic bias of $+\frac{d_{ms} - d_{sm}}{2}$** whenever forward and reverse propagation delays differ (Probe 2B: 800 ns asymmetry injects +400 ns bias). IEEE 802.1Qbv Time-Aware Shapers eliminate queuing variance via synchronized Gate Control Lists, while **Huygens** (`Geng et al., NSDI 2018`) combines coded packet-pair probes, an SVM queuing classifier, and transitive mesh **cycle consistency** ($\sum \hat{\theta}_{ij} = 0$) to suppress isolated asymmetric links (Probe 2B: cycle-median eliminates +800 ns single-link bias to 0.0 ns in $K_5$) and reach tens-of-nanoseconds accuracy on commodity NICs.
4. **Timescale anomalies—leap-second smearing mismatches and VM live migration—shatter distributed clock-skew budgets.** While the **28th CGPM (October 2026, Resolution 5)** formally adopted continuous UTC effective **May 20, 2027** (widening $|UT1 - UTC|$ tolerance to 3,600 s and superseding the 27th CGPM 2022 "by 2035" horizon), historical and legacy leap-second smearing policies remain incompatible across administrative domains: mixing step-UTC, 24 h linear smear, 24 h cosine smear, 20 h linear smear, and `fbclock` v2's `62500s` smear produces **83.33 ms to 500.00 ms** peak wall-clock divergence (Probe 2B)—**25×–125× larger than TrueTime's 4 ms $\varepsilon$**—explaining why `fbclock` v3 serves pure TAI internally and explicitly refuses to smear (`fbclock.c:801`). Across VM live migration, `kvmclock` (`pvclock_vcpu_time_info`) signals pauses via `PVCLOCK_GUEST_STOPPED`, while blackout durations exceeding `maxOffset / 2` trigger fatal clock-jump panics in HLC clusters and divergence between `CLOCK_MONOTONIC` and `CLOCK_BOOTTIME`.
5. **Sound temporal type systems separate timescales, locality domains, and interval partial orders—and MUST NOT implement total-order `Ord` on uncertainty intervals.** Standard-library types (`rust-lang/rust` `std::time::{Instant, SystemTime}`) conflate suspend semantics and mask monotonicity bugs via silent zero-saturation in `Instant::duration_since`. Explicit timescale libraries (`nyx-space/hifitime`) separate continuous atomic scales (`TAI`, `GPST`, `TT`) from `UTC`. Crucially, the sound epistemic order $A <_{\text{cert}} B \iff A.\text{latest} < B.\text{earliest}$ is a **strict interval order**, *not* a weak order: incomparability ($A \parallel B$) is **non-transitive** (`A=[0,10], B=[8,18], C=[15,25]` satisfies $A \parallel B$ and $B \parallel C$ yet $A <_{\text{cert}} C$, Probe 2B), making any `Ord::cmp` / `BTreeMap` key wrapping an epistemic interval mathematically unsound.

## Applicability

This report synthesizes normative standards, theoretical bounds, peer-reviewed distributed systems papers, production C/Go/Rust implementations, and reproducible Python micro-probes:

- **Distributed consensus & bounded-uncertainty clocks:** Findings on CockroachDB HLC apply directly to `cockroachdb/cockroach` @ `d30c905fff79ef825adc96bcc647f1872a90f2ff` (`pkg/util/hlc/{hlc.go,timestamp.go}`, `pkg/kv/kvpb/errors.proto`). Findings on open-source PTP-backed TrueTime/WOU clocks apply directly to `facebook/time` @ `62fc415c683e157653af71e4ac34216eedaf5879` (`fbclock/{fbclock.h,fbclock.c,README.md}`), distinguishing **v2** (leap-smearing with `SMEAR_DURATION = 62500`) from **v3** (4096-byte multi-source SHM, pure TAI anchor, no smearing). Google Spanner TrueTime findings are grounded in Corbett et al. (OSDI 2012 / ACM TOCS 2013, `DOI: 10.1145/2491245`).
- **Hardware/software network sync:** PTP timestamp processing findings apply to `richardcochran/linuxptp` @ `227bbd4715bf4cb735be4947e987032f41457585` (`clock.c`, `tsproc.c`) and IEEE Std 1588-2019; TSN scheduled traffic findings refer to IEEE Std 802.1Qbv-2015 / 802.1Q-2022; Huygens findings refer to Geng et al. (USENIX NSDI 2018).
- **OS kernels, virtualization, and temporal type libraries:** Linux clock IDs, NTP `adjtimex` flags, and x86 KVM paravirtualized clocks apply to `torvalds/linux` @ `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd` (`include/uapi/linux/{time.h,timex.h}`, `arch/x86/include/asm/pvclock-abi.h`, `arch/x86/kernel/kvmclock.c`). Rust standard-library behavior applies to `rust-lang/rust` @ `b0b600668bb9b4a897e2299b0a44289d42276545` (`library/std/src/time.rs`); multi-timescale epoch typing applies to `nyx-space/hifitime` @ `e258220164f6f6a488e2e1d7083587a540990567` (`src/timescale/mod.rs`, `src/epoch/leap_seconds.rs`).
- **Relationship among subjects:** Hardware sync protocols (PTP, Huygens, GNSS/atomic masters) determine the physical error bound $\varepsilon$ and drift rate $\rho$; OS kernels (`CLOCK_TAI`/`CLOCK_MONOTONIC_RAW`/`kvmclock`) propagate (or corrupt) that bound across syscalls, leap seconds, and VM migrations; distributed clock layers (TrueTime, `fbclock`, HLC) expose or hide that bound to consensus protocols; and temporal type systems enforce timescale, locality, and interval-order invariants at compile time.

## Findings

### 1. Theoretical Impossibility Results and Byzantine Clock Synchronization

*Basis: publication (Lundelius & Lynch, 1984; Lamport & Melliar-Smith, JACM 1985; Dolev, Halpern, Strong, JCSS 1986) + execution (Probe 2B) + derived*

Before evaluating any engineering protocol, three classical theorems establish hard physical and adversarial limits that no software algorithm can bypass:

#### 1.1 Path-Delay Uncertainty Lower Bound (Lundelius & Lynch, 1984)

In *"An Upper and Lower Bound for Clock Synchronization"* (*Information and Control*, 1984, `DOI: 10.1016/s0019-9958(84)80033-9`), Lundelius and Lynch consider a fully connected network of $n$ non-faulty processes with **zero drift** ($\rho = 0$) whose message delivery delays lie in $[l, u]$ (delay uncertainty $\delta_{\text{net}} = u - l$). They prove that **no clock synchronization algorithm can guarantee worst-case skew tighter than**:

$$\varepsilon_{\min} \ge (u - l)\left(1 - \frac{1}{n}\right)$$

The proof exploits indistinguishability under **time-shifting executions**: shifting process $i$'s clock forward by $+\Delta$ while lengthening incoming delays to $i$ by $+\Delta$ and shortening outgoing delays from $i$ by $-\Delta$ leaves every local message-receipt timestamp at every process bitwise identical! This theorem is the theoretical root of IEEE 1588 PTP's path-asymmetry blindness (Section 3.1): round-trip timing measurements alone can measure $d_{ms} + d_{sm}$, never $d_{ms} - d_{sm}$.

#### 1.2 Byzantine Fault-Tolerance Threshold ($n \ge 3f + 1$) & Interactive Convergence

In *"Synchronizing Clocks in the Presence of Faults"* (*JACM*, 1985, `DOI: 10.1145/2455.2457`), Lamport and Melliar-Smith present three fault-tolerant algorithms tolerating $f$ arbitrary (including "two-faced" equivocating) Byzantine clocks:

1. **Interactive Convergence (`CNV`):** Every resynchronization period $R$, each process $p$ reads the offset $\Delta_{pq}$ of every peer $q$; any reading $|\Delta_{pq}| > \delta$ (a fixed fault-rejection threshold) is replaced by $0$ (its own clock), and $p$ adjusts its clock by the mean $\frac{1}{n}\sum_{q=1}^{n} \tilde{\Delta}_{pq}$. `CNV` requires **$n \ge 3f + 1$** and requires no cryptographic signatures.
2. **Interactive Consistency (`COM` / `CSM`):** Uses Byzantine agreement (oral messages `COM`, requiring $n \ge 3f + 1$, or signed messages `CSM`, tolerating $n \ge 2f + 1$ under unforgeable signatures) so all non-faulty nodes agree on an identical vector of clock readings and take the **median**, achieving tighter skew at higher message complexity.

**Impossibility for $n \le 3f$ without signatures:** Dolev, Halpern, and Strong (*JCSS*, 1986, `DOI: 10.1016/0022-0000(86)90028-0`) proved that in the unauthenticated Byzantine model, achieving bounded clock synchronization is **impossible whenever $n \le 3f$** (even with zero drift and exact message delays).

**Executable verification (Probe 2B):**
- For **$n = 3, f = 1$ ($n = 3f$)** with honest clocks $A = 0, B = 100$ and threshold $\delta = 100$, a two-faced Byzantine node $M$ reports $a - \delta$ to $A$ and $b + \delta$ to $B$ in every round. Neither reading exceeds the $\delta$ filter, so $A_{\text{next}} = (a + (a-\delta) + b)/3 = a$ and $B_{\text{next}} = (a + b + (b+\delta))/3 = b$: after 5 rounds, $|B - A|$ remains **`100.0`** (**zero convergence**).
- For **$n = 4, f = 1$ ($n = 3f + 1$)** with honest clocks $A = 0, B = 100, C = 50$ under the same worst-case $\pm\delta$ adversarial pull, the spread contracts from `100.0` to **`66.70`** in 5 rounds (approaching the exact algebraic fixed-point spread $\frac{2\delta}{3} \approx 66.67$ under continuous maximal Byzantine skew injection).

---

### 2. Bounded-Uncertainty Epistemic Clocks: Spanner TrueTime & Meta `fbclock` vs. Hybrid Logical Clocks

*Basis: publication (Corbett et al., OSDI 2012 / ACM TOCS 2013; Kulkarni et al., OPODIS 2014) + source (`facebook/time/fbclock/{fbclock.h,fbclock.c}`, `cockroachdb/cockroach/pkg/util/hlc/{hlc.go,timestamp.go}`, `pkg/kv/kvpb/errors.proto`) + execution (Probe 2A)*

#### 2.1 Google Spanner TrueTime & External Consistency Proof

Spanner (`Corbett et al., ACM TOCS 2013`, `DOI: 10.1145/2491245`) replaces point-valued wall clocks with an explicit uncertainty-interval API backed by dual-modality time masters (GPS receivers + rubidium atomic clocks, guarding against correlated antenna/spoofing or oscillator failures):

```text
TT.now()      -> TTinterval { earliest, latest }   // Invariant: earliest <= t_abs <= latest
TT.after(t)   -> bool                              // true iff t < TT.now().earliest
TT.before(t)  -> bool                              // true iff TT.now().latest < t
```

Each host daemon polls time masters every ~30 s, producing a characteristic sawtooth uncertainty half-width $\varepsilon(t) = \varepsilon_0 + \rho \cdot (t - t_{\text{sync}})$, with worst-case local crystal drift bound $\rho = 200\,\mu\text{s/s}$ (200 ppm), yielding $\varepsilon \in [1\,\text{ms}, 7\,\text{ms}]$ (average ~4 ms) in production datacenters.

**External Consistency (Strict Serializability) Invariant:** If read-write transaction $T_2$ starts in real time *after* $T_1$ commits ($t_{\text{abs}}^{\text{start}}(T_2) > t_{\text{abs}}^{\text{commit}}(T_1)$), then $s_1 < s_2$. Spanner enforces this via two rules:
1. **Start rule:** Coordinator picks commit timestamp $s_i \ge \text{TT.now().latest}$ (computed after acquiring all locks).
2. **Commit-Wait rule:** Coordinator holds locks and delays making $T_i$'s writes visible to clients until **`TT.after(s_i)`** returns `true` (waiting up to $2\varepsilon$ in real time).

**3-line proof:**
- By Commit-Wait, $s_1 < \text{TT.now}(t_{\text{abs}}^{\text{commit}}(T_1)).\text{earliest} \le t_{\text{abs}}^{\text{commit}}(T_1)$.
- By real-time precedence, $t_{\text{abs}}^{\text{commit}}(T_1) < t_{\text{abs}}^{\text{start}}(T_2)$.
- By Start rule, $t_{\text{abs}}^{\text{start}}(T_2) \le \text{TT.now}(t_{\text{abs}}^{\text{start}}(T_2)).\text{latest} \le s_2$.
- Transitivity yields $s_1 < s_2$. $\square$

**Empirical fragility to 1 ns wait violation or unmodeled drift (Probe 2A):** Across 10,000 adversarial random skew trials ($|e_i| \le 4\,\text{ms}$), full commit-wait produced **`0/10000`** inversions. However:
- Cutting commit-wait **1 ns short** (`t_done = t1 + 2*eps - 1`) under worst-case opposite skews ($e_1 = +\varepsilon, e_2 = -\varepsilon$) yields `s1 = 10008000000`, `s2 = 10007999999` (`s2 - s1 = -1 ns`)—an immediate external consistency violation.
- Breaching the physical clock error bound by just **500 ns** ($|e_i| = \varepsilon + 500\,\text{ns}$, e.g. from unmonitored holdover drift or asymmetric path delay) breaks external consistency even under full commit-wait (`s2 - s1 = -999 ns`). Thus, TrueTime shifts safety from *algorithmic assumption* to **verified physical metrology**.

#### 2.2 Open-Source TrueTime Engineering: Meta `fbclock` (`facebook/time` @ `62fc415c...`)

Direct inspection of `facebook/time/fbclock/{fbclock.h,fbclock.c,README.md}` documents a complete production open-source TrueTime implementation built over NIC PTP Hardware Clocks (PHCs) and `ptp4l`:

- **Interval API (`fbclock.h:244–247, 373–386`):** `struct fbclock_truetime { uint64_t earliest_ns; uint64_t latest_ns; }` populated via `fbclock_gettime` (TAI) and `fbclock_gettime_utc` (UTC), plus `fbclock_gettime_past` which retroactively lifts a host-local `CLOCK_REALTIME` timestamp (e.g., kernel `SO_TIMESTAMPING` software TX timestamp) into a bounded `[earliest_ns, latest_ns]` interval within $\pm\text{FBCLOCK\_MAX\_EXTRAPOLATION\_NS}$.
- **Lock-free cache-line-isolated seqlock SHM (`fbclock.h:125–231`, `fbclock.c:48–92, 155–225`):**
  - Both v2 (`fbclock_shmsection`) and v3 (`fbclock_data_section`, 4096-byte page supporting 32 independent `FBCLOCK_SOURCE_*` bits: `PTP`, `PRTC`, `NTP`) place each `atomic_uint64 seq` on its own `alignas(64)` cache line so writers to one section never invalidate readers of another.
  - Writers mark `seq` odd with `atomic_thread_fence(memory_order_release)`, write payload, then store even `seq`; readers retry up to `FBCLOCK_MAX_READ_TRIES = 1000` with `memory_order_acquire`, returning `FBCLOCK_E_CRC_MISMATCH` (`-8`) on persistent contention.
- **Exact WOU & fail-closed guards (`fbclock.c:592–666, 763–812`):**
  - Linear extrapolation from the daemon's periodic PHC/sysclock anchor (`CLOCK_MONOTONIC_RAW` preferred over `CLOCK_REALTIME`):
    $$\text{phc\_now} = \text{phc\_anchor} + \Delta_{\text{sys}} + \frac{\Delta_{\text{sys}} \cdot \text{coef\_ppb}}{10^9}$$
    *(Notably, `fbclock.c:640–645` explicitly casts `NANOSECONDS_IN_SECONDS` to `int64_t` because unsigned `uint64_t` promotion of a negative `coef_ppb` product silently wrapped to $\approx 2^{64}/10^9 \approx 18.45\,\text{s}$!)*
  - Window of Uncertainty growth (`fbclock_window_of_uncertainty`, `fbclock.c:592–604`):
    $$W(\Delta t_{\text{holdover}}) = \text{error\_bound\_ns} + \left\lfloor \frac{\text{holdover\_multiplier\_ns}}{2^{16}} \cdot \Delta t_{\text{holdover}} \right\rfloor$$
    where `holdover_multiplier_ns` is fixed-point Q16.16 ns/s and $\Delta t_{\text{holdover}} = \max(0, \text{phc\_now} - \text{ingress\_time\_ns})$.
  - **Fail-closed error codes (`fbclock.h:52–70`, `fbclock.c:630–639, 733–736`):** Returns `FBCLOCK_E_DATA_STALE` (`-9`) if `diff_ns < 0` or `diff_ns > 10s` (`FBCLOCK_MAX_EXTRAPOLATION_NS`), `FBCLOCK_E_PHC_IN_THE_PAST` (`-7`) if `ingress_time_ns > phc_time_ns`, and `FBCLOCK_E_WOU_TOO_BIG` (`-6`) if either bound saturates at `UINT32_MAX` (~4.29 s) or exceeds caller-configured `fbclock_options.max_wou_ns`.
- **Explicit anti-midpoint contract (`fbclock.h:389–416`):** The header documents formally: *"the WOU is a bound, not a probability distribution. Every point in `[earliest_ns, latest_ns]` is equally consistent with the guarantee... event A provably happens-before event B only when `A.latest_ns < B.earliest_ns`."*
- **Version evolution (`v2` vs. `v3`, `fbclock.c:114–117, 801–804, 945–1009`):** `fbclock` v2 applies linear leap-second smearing over **`SMEAR_DURATION = 62500` seconds** (~17.36 hours), whereas `fbclock` v3 uses pure TAI anchors (`UTC_TAI_OFFSET_NS = -37e9`) and **never smears**.

#### 2.3 Hybrid Logical Clocks (Kulkarni et al., OPODIS 2014 & `cockroachdb/cockroach` @ `d30c905f...`)

Hybrid Logical Clocks (`Kulkarni, Demirbas, Madeppa, Avva, Leone, OPODIS 2014`, `DOI: 10.1007/978-3-319-14472-6_2`) represent each timestamp as a lexicographically ordered pair `(WallTime, Logical)` (`int64` ns + `int32` logical counter in `cockroachdb/cockroach` `pkg/util/hlc/timestamp.go:20–62`), maintaining two simultaneous invariants:
1. **Causality:** $e \to f \implies (l_e, c_e) <_{\text{lex}} (l_f, c_f)$.
2. **Bounded physical closeness:** Under bounded cluster skew $\varepsilon$, $|l_j - \text{pt}_j| \le \varepsilon$, preventing unbounded drift from physical time.

Direct inspection of `cockroachdb/cockroach` (`d30c905fff79ef825adc96bcc647f1872a90f2ff`, `pkg/util/hlc/{hlc.go,timestamp.go}` & `pkg/kv/kvpb/errors.proto`) reveals five production-hardened mechanisms beyond the textbook paper:

1. **Capability-typed `ClockTimestamp` (`timestamp.go:328–341`):** Go defines `type ClockTimestamp Timestamp` as a distinct nominal type carrying the invariant that the value *actually originated from an HLC clock in the cluster*. `Clock.NowAsClockTimestamp()` returns `ClockTimestamp`, and `Clock.Update(rt ClockTimestamp)` / `UpdateAndCheckMaxOffset(ctx, rt ClockTimestamp)` accept *only* `ClockTimestamp`—preventing user-supplied or future synthetic timestamps from poisoning cluster HLCs (bypassing requires explicit `UnsafeToClockTimestamp()`).
2. **`NowAsClockTimestamp()` & `Update()` exact transitions (`hlc.go:422–437, 471–498`):**
   - Local event (`Now`): if `c.mu.timestamp.WallTime >= physicalClock`, increments `Logical++`; else stores `WallTime = physicalClock` atomically and resets `Logical = 0`.
   - Remote receive (`UpdateAndCheckMaxOffset`, `hlc.go:517–535`): computes `offset = rt.WallTime - physicalClock`; if `c.maxOffset > 0 && offset > c.maxOffset`, rejects the RPC with `errUntrustworthyRemoteWallTimeErr` instead of dragging the node into the far future.
3. **Active jump detection & self-termination (`hlc.go:254–354, 385–407, 439–451`):**
   - Distinguishes **`MaxOffset`** (the operator-promised maximum skew used for lease handoff and single-key linearizability) from **`ToleratedOffset`** (heartbeat-measured skew threshold triggering self-termination via `RemoteClockMonitor`).
   - Polls physical time every `toleratedForwardClockJump / 2` where **`toleratedForwardClockJump = c.maxOffset / 2`** (`hlc.go:257–259, 296`), calling **`c.logger.Fatalf`** (halting the node) if a forward jump $\ge \text{maxOffset}/2$ occurs (e.g., VM live migration pause or NTP step!). Backward jumps $> \text{maxOffset}/10$ increment `monotonicityErrorsCount` and warn (`hlc.go:391–394`).
   - Enforces a persisted **`wallTimeUpperBound`** (`RefreshHLCUpperBound`, `hlc.go:441–451, 559–583`): if the clock ever exceeds the last persisted upper bound (protecting against clock-jump corruption across restarts/leases), the node immediately calls `Fatalf`.
4. **Uncertainty-interval read restarts (`pkg/kv/kvpb/errors.proto:114–137`):** Because CockroachDB does **not** perform Spanner's commit-wait, a transaction $T_2$ starting on a slower node $N_2$ at timestamp $t_r$ may encounter a committed write at timestamp $t_v \in (t_r, t_r + \text{MaxOffset}]$ that actually committed *before* $T_2$ started in real time. Rather than returning a stale read, the replica raises **`ReadWithinUncertaintyIntervalError`** (carrying `read_timestamp`, `local_uncertainty_limit`, `global_uncertainty_limit`, `value_timestamp`), causing $T_2$ to advance its timestamp to `value_timestamp` and retry!
5. **Exact semantic boundary vs. TrueTime (Probe 2A):** With `skew = 200 ms <= max_offset = 250 ms`, if $T_1$ writes key $K_1$ on fast node $N_1$ (`+100 ms`), returns immediately, and the client initiates $T_2$ out-of-band on slow node $N_2$ (`-100 ms`):
   - If $T_2$ **reads $K_1$**, CockroachDB's uncertainty interval catches `hlc2 < hlc1 <= hlc2 + max_offset` (`caught_by_uncert_restart = True`), preserving single-key linearizability.
   - If $T_2$ **writes a disjoint key $K_2$**, there is no key conflict and no commit-wait, so $T_2$ commits at `hlc2 < hlc1` (`-199.0 ms` real-time inversion, `disjoint_write_inversion = True`)—meaning HLC without commit-wait provides **serializability + single-key/causal linearizability**, NOT full cross-key external consistency (strict serializability) for out-of-band causally disconnected transactions. Note also `hlc.go:332–335`'s explicit source caveat: if real clock skew exceeds `MaxOffset`, stale reads become possible and even serializability is explicitly labeled *"conjecture"* rather than verified!

#### 2.4 Distributed Time Mechanism Comparison Matrix

| Property | Google Spanner TrueTime | Meta `fbclock` (v2 / v3) | CockroachDB HLC | Lamport / Vector Clocks |
|---|---|---|---|---|
| **Clock Representation** | `[earliest, latest]` (`TTinterval`) | `{earliest_ns, latest_ns}` (`fbclock_truetime`) | `(WallTime: i64, Logical: i32)` + `ClockTimestamp` | Logical integer / $N$-vector |
| **Hardware Requirement** | GPS + Rubidium/Atomic masters | NIC PHC + `ptp4l` (v3 also supports NTP fallback) | Commodity NTP/Chrony (operator `MaxOffset`) | None |
| **Typical Uncertainty ($\varepsilon$)** | 1–7 ms (mean ~4 ms) | Sub-$\mu$s to ~100 $\mu$s (PTP); ms (NTP) | 50–500 ms (`MaxOffset` bound) | Unbounded (no physical time) |
| **Strict Serializability (Out-of-Band)?** | **Yes** (via $2\varepsilon$ commit-wait) | **Yes** (if paired with commit-wait) | **No** for disjoint out-of-band writes (yes for overlapping keys via uncertainty restart) | **No** (causal only) |
| **Failure Mode on Skew Breach** | Unbounded/elevated $\varepsilon$ stalls commits; silent breach breaks external consistency | Fail-closed (`FBCLOCK_E_WOU_TOO_BIG`, `FBCLOCK_E_DATA_STALE`, `FBCLOCK_E_PHC_IN_THE_PAST`) | Node self-termination (`Fatalf` on forward jump $\ge \text{MaxOffset}/2$ or `RemoteClockMonitor` $> \text{ToleratedOffset}$) | N/A |

---

### 3. Sub-Microsecond Hardware & Software Sync: IEEE 1588 PTP, 802.1Qbv TSN, and Huygens

*Basis: normative specification (IEEE 1588-2019, IEEE 802.1Qbv) + source (`richardcochran/linuxptp` `tsproc.c`, `clock.c`) + publication (Geng et al., USENIX NSDI 2018) + execution (Probe 2B)*

#### 3.1 IEEE 1588-2019 (PTPv2.1) & `linuxptp` Offset/Delay Equations

IEEE 1588 achieves nanosecond-class synchronization by stamping Ethernet frames directly at the **NIC PHY/MAC hardware layer** (Linux `SOF_TIMESTAMPING_TX_HARDWARE` / `RX_HARDWARE` / `RAW_HARDWARE`), removing OS kernel scheduling, interrupt coalescing, and TCP/IP stack jitter. In an End-to-End (E2E) two-step exchange between Master ($M$) and Slave ($S$):
- $M$ transmits `Sync` at hardware time $t_1$ (communicated in `Follow_Up`, or embedded on-the-fly in one-step hardware); $S$ receives `Sync` at local PHC time $t_2$.
- $S$ transmits `Delay_Req` at local PHC time $t_3$; $M$ receives `Delay_Req` at master time $t_4$ and returns $t_4$ in `Delay_Resp`.

Direct inspection of `richardcochran/linuxptp` (`227bbd4715bf4cb735be4947e987032f41457585`, `tsproc.c:124–228`) reveals the exact implementation formulas:

```c
/* tsproc.c:128–134: get_raw_delay (t2, t3 in local clock scaled by clock_rate_ratio rr) */
delay = ((t2 - t3) * rr + (t4 - t1)) / 2;

/* tsproc.c:212–213: tsproc_update_offset */
offset = (t2 - t1) - delay;
```

Notice the critical frequency-ratio scaling `(t2 - t3) * rr`: because $t_2$ and $t_3$ are stamped by the un-syntonized local oscillator while $t_1$ and $t_4$ come from the master oscillator, `linuxptp` scales `t2 - t3` by the estimated frequency ratio `rr` before averaging with `t4 - t1`. Furthermore, `clock.c:936–937, 969–972` converts between PTP's native continuous **TAI** timescale (`PTP_TIMESCALE`) and local UTC by subtracting `utc_offset * NS_PER_SEC` (37 s).

**Fundamental Path Asymmetry Bias:** Let the true slave-minus-master offset be $\theta$, forward propagation delay be $d_{ms}$, and reverse delay be $d_{sm}$. Then $t_2 - t_1 = d_{ms} + \theta$ and $t_4 - t_3 = d_{sm} - \theta$ (for $r = 1$). Substituting into `tsproc.c`:

$$\hat{d} = \frac{d_{ms} + d_{sm}}{2}, \qquad \hat{\theta} = (d_{ms} + \theta) - \frac{d_{ms} + d_{sm}}{2} = \theta + \frac{d_{ms} - d_{sm}}{2}$$

Any uncalibrated path asymmetry $\Delta = d_{ms} - d_{sm}$ (caused by asymmetric switch queuing, asymmetric fiber lengths, different forward/reverse wavelength chromatic dispersion in single-fiber WDM optics, or asymmetric PHY serializer/deserializer latency) injects an **undetectable systematic offset error of $+\Delta / 2$**. In **Probe 2B**, setting $d_{ms} = 2400\,\text{ns}, d_{sm} = 1600\,\text{ns}$ (800 ns asymmetry) yields `est_delay = 2000.0 ns` and `bias = +400.0 ns`—exactly $+\Delta / 2$. IEEE 1588-2019 mitigates queuing asymmetry inside the network via **Boundary Clocks (BC)** (terminating and regenerating PTP hop-by-hop) and **Transparent Clocks (TC)** (measuring exact hardware residence time inside each switch and accumulating it in the packet's 64-bit `correctionField`, in units of $2^{-16}\,\text{ns}$), while static link asymmetry still requires manual `delayAsymmetry` calibration per link.

#### 3.2 IEEE 802.1Qbv Time-Aware Shaper (TSN) Co-Design

IEEE 802.1Qbv-2015 (folded into IEEE 802.1Q-2022) couples sub-microsecond clock synchronization (IEEE 802.1AS gPTP profile of IEEE 1588) directly to switch egress scheduling:
- Each egress port runs a cyclic **Gate Control List (GCL)** synchronized across every bridge in the TSN domain, opening exclusive transmission gates for scheduled real-time traffic classes while closing best-effort queues behind a **guard band** (up to one max-MTU frame time, reducible via IEEE 802.1Qbu frame preemption).
- This creates a bidirectional hardware-timing loop: **bounded clock sync enables zero-queuing deterministic forwarding windows**, and **zero-queuing windows suppress PTP queuing asymmetry**, tightening synchronization precision further.

#### 3.3 Huygens (USENIX NSDI 2018): Coded Probes, SVM Filtering, and the Natural Network Effect

Deploying PTP Boundary/Transparent Clocks across every datacenter Top-of-Rack and spine switch is prohibitively expensive in brownfield clouds. **Huygens** (`Geng et al., USENIX NSDI 2018`) achieves **tens-of-nanoseconds (within ~100 ns)** synchronization across standard commodity datacenter switches without hardware Transparent Clocks via three coupled techniques:

1. **Coded Probes (back-to-back packet pairs):** Instead of isolated single probes, pairs of packets are transmitted back-to-back; if the inter-arrival gap expands or compresses at the receiver relative to the inter-departure gap, queuing noise occurred and the probe pair is immediately discarded before inference.
2. **Support Vector Machine (SVM) Min-Delay Boundary Classification:** Plotting $(t_1, t_2 - t_1)$ for forward probes and $(t_4, t_3 - t_4)$ for reverse probes produces two point clouds whose tight lower/upper envelopes correspond to **pure unqueued propagation delay**; a linear SVM separates the two unqueued boundaries to infer pairwise offset $\hat{\theta}_{ij}$ and frequency drift while rejecting asymmetric queuing outliers.
3. **Natural Network Effect (Transitive Cycle Closure):** Over any closed cycle $i \to j \to k \to i$ of clocks, true pairwise offsets satisfy **Kirchhoff's loop law**:
   $$\theta_{ij} + \theta_{jk} + \theta_{ki} = 0$$
   Therefore, any nonzero cycle residual $r_{ijk} = \hat{\theta}_{ij} + \hat{\theta}_{jk} - \hat{\theta}_{ik}$ directly exposes uncompensated link asymmetry or noise! Solving a global graph consistency problem (or robust median/RANSAC across triangles) cancels isolated biased links without hardware switch support.
   - **Executable verification (Probe 2B):** On a 5-node complete mesh $K_5$ where link `(0, 1)` suffers a **+800 ns** uncompensated asymmetry bias while the remaining 9 links are unbiased, all three triangles `(0, 1, k)` ($k \in \{2, 3, 4\}$) immediately flag residual **`+800.0 ns`**; unweighted 1+2-hop averaging suppresses the error by $4\times$ to `+200.0 ns`, and **cycle-median estimation eliminates the +800 ns bias completely (`+0.0 ns` error)**.

---

### 4. OS Timescales, Leap-Second Smearing Hazards, CGPM Continuous UTC, and VM Live Migration

*Basis: normative specification (POSIX.1, 27th CGPM Res. 4, 28th CGPM Res. 5) + source (`torvalds/linux` `time.h`, `timex.h`, `pvclock-abi.h`, `kvmclock.c`; `facebook/time/fbclock/fbclock.c`; `nyx-space/hifitime/src/epoch/leap_seconds.rs`) + execution (Probe 2B)*

#### 4.1 Linux Clock Domains & NTP Leap-Second State Machine

Direct inspection of `torvalds/linux` (`4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`, `include/uapi/linux/time.h:49–77` and `include/uapi/linux/timex.h:139–205`) enumerates the exact kernel clock domains and their radically different behavioral invariants:

| Linux Clock ID | Numeric ID (`time.h`) | Step Backwards (NTP/Leap)? | Slewed by NTP/PTP? | Advances During System Suspend? | Timescale / Primary Use |
|---|---:|---|---|---|---|
| `CLOCK_REALTIME` | `0` | **Yes** (NTP step, `settimeofday`, leap step) | Yes | Yes | POSIX UTC wall time (non-monotonic, ignores leap seconds in `time_t`) |
| `CLOCK_MONOTONIC` | `1` | No (barring hardware/VM bugs) | **Yes** (frequency slewed) | **No** (frozen while suspended) | Elapsed timeouts on active host (matches Rust Unix `Instant`) |
| `CLOCK_MONOTONIC_RAW` | `4` | No | **No** (raw hardware crystal/TSC) | **No** | Short-term local anchor (`fbclock` v2/v3 primary anchor to avoid double-slewing!) |
| `CLOCK_BOOTTIME` | `7` | No | Yes | **Yes** (includes suspend duration) | Lease expirations, token TTLs, and wake-aware timers across suspend |
| `CLOCK_TAI` | `11` | No (unless `ADJ_TAI` misconfigured) | Yes | Yes | Continuous SI atomic time (`TAI = UTC + 37s` since 2017-01-01; **warning:** defaults to `tai=0` until daemon calls `adjtimex(ADJ_TAI)`!) |
| `CLOCK_AUX` (`+0..7`) | `16..23` | Independent | Independently steered | Independent | Auxiliary timekeepers decoupled from core system timekeeper |

In `include/uapi/linux/timex.h:176–205`, kernel leap-second insertion/deletion is driven by `STA_INS` (`0x0010`) and `STA_DEL` (`0x0020`), stepping the kernel through `TIME_OK (0) -> TIME_INS (1) -> TIME_OOP (3, leap in progress) -> TIME_WAIT (4)`. Because POSIX `time_t` defines every UTC day as strictly `86,400` seconds (omitting leap seconds), a positive leap second (`23:59:60 UTC`) forces `CLOCK_REALTIME` to **step backward by 1 full second**, repeating an entire second of `time_t` values (`t = 1483228799` occurred twice on 2016-12-31).

#### 4.2 Abolition of the Leap Second: 27th CGPM (2022) → 28th CGPM (October 2026)

- Historically, ITU-R TF.460 mandated keeping $|UT1 - UTC| < 0.9\,\text{s}$ via irregular 1-second steps (27 IERS positive leap seconds inserted between 1972-01-01 and 2017-01-01, bringing `TAI - UTC = 37 s`; verified in `nyx-space/hifitime` `src/epoch/leap_seconds.rs:63–91`).
- At the **27th CGPM (November 2022, Resolution 4)**, member states voted to discontinue leap seconds by or before 2035.
- At the **28th CGPM (Versailles, October 13–15, 2026, Resolution 5)**, accelerating the timeline to preempt the unprecedented software risk of a **negative leap second** (`23:59:58 -> 00:00:00`, never exercised in production infrastructure), BIPM formally adopted a **continuous UTC timescale effective May 20, 2027**, widening the allowable $|UT1 - UTC|$ bound from $0.9\,\text{s}$ to **$3{,}600\,\text{s}$ (1 hour)**.
- **Engineering implication:** Even after May 20, 2027 freezes the `TAI - UTC` offset (at 37 s unless an intervening leap second occurs before then), historical timestamps across 1972–2016 retain all 27 leap-second discontinuities, and legacy leap-smearing configurations remain deployed in existing NTP fleets.

#### 4.3 Cross-Domain Leap-Second Smear Divergence (Probe 2B)

To avoid the backward 1-second step, cloud operators adopted **leap smearing** (gradually slewing UTC frequency across a multi-hour window). However, because smearing alters the effective length of a second without a universal international wire standard, **cross-domain interoperability between differently smeared (or unsmeared) clocks breaks distributed uncertainty bounds catastrophically**:

| Clocks Compared Across Positive Leap Second ($T_0 = 0$) | Peak Wall-Clock Divergence | Time of Peak ($t - T_0$) | Ratio vs. Spanner 4 ms $\varepsilon$ |
|---|---:|---:|---:|
| **Step-UTC vs. 24 h Linear Smear** (Google Public NTP / AWS, $-11.57\,\text{ppm}$, $[-12\text{h}, +12\text{h}]$) | **500.00 ms** | $0\,\text{s}$ | **125×** |
| **24 h Linear Smear vs. Post-Aligned 62,500 s Smear** (`fbclock` v2 `SMEAR_DURATION = 62500`, $[0, +17.36\text{h}]$) | **500.00 ms** | $0\,\text{s}$ | **125×** |
| **24 h Linear Smear vs. 24 h Cosine Smear** ($\frac{1 - \cos(\pi u)}{2}$) | **105.26 ms** | $-24{,}220\,\text{s}$ ($\pm 6.73\text{h}$) | **26×** |
| **24 h Linear Smear vs. Legacy 20 h Linear Smear** ($[-10\text{h}, +10\text{h}]$) | **83.33 ms** | $\pm 36{,}000\,\text{s}$ ($\pm 10\text{h}$) | **21×** |

*Basis: execution (Probe 2B) + source (`facebook/time/fbclock/fbclock.c:117, 801–804, 945–1009`).*
Because a 500 ms divergence between a 24 h linear-smear cloud VM and a step-UTC or `fbclock`-v2 peer **exceeds CockroachDB's default 250–500 ms `MaxOffset`** and obliterates PTP/TrueTime bounds, modern high-assurance distributed systems (including `fbclock` v3, `fbclock.c:801`: *"The anchor is TAI, and v3 never smears"*) anchor all consensus timestamps on **continuous TAI** and reserve UTC strictly for human display formatting at API edges.

#### 4.4 Virtual Machine Live Migration and Hypervisor Clocks (`kvmclock`)

Direct inspection of `torvalds/linux` (`4405c18c...`, `arch/x86/include/asm/pvclock-abi.h:26–46` and `arch/x86/kernel/kvmclock.c:75–210, 264–372`) illuminates how hypervisors virtualize time across physical host migration:

- **Shared guest/host ABI (`pvclock-abi.h:26–35`):** Each vCPU maps a 32-byte packed `struct pvclock_vcpu_time_info` containing an even/odd seqlock `u32 version`, `u64 tsc_timestamp`, `u64 system_time`, `u32 tsc_to_system_mul`, `s8 tsc_shift`, and `u8 flags`. Guest reads loop until `version` is even and unchanged (`kvmclock.c:99–103`), computing `system_time + scale(rdtsc() - tsc_timestamp)` in userland vDSO (`VDSO_CLOCKMODE_PVCLOCK`) **only if** `PVCLOCK_TSC_STABLE_BIT` (`1<<0`) is advertised (`kvmclock.c:276–279`).
- **Live-migration blackout & pause semantics (`kvmclock.c:157–171`):** During live migration's stop-and-copy blackout (typically 50 ms–2,000+ ms depending on dirty-page rate), the destination hypervisor updates `TSC_OFFSET` / `TSC_SCALING` (if CPU TSC frequencies differ) and sets **`PVCLOCK_GUEST_STOPPED` (`1<<1`)**. On resume, the guest's `kvm_check_and_clear_guest_paused()` clears the flag and calls `pvclock_touch_watchdogs()` so the kernel softlockup detector does not panic.
- **Hazards to userland distributed systems:**
  1. **Silent blackout vs. HLC `MaxOffset` panic:** Userland processes receive no notification of `PVCLOCK_GUEST_STOPPED`. If the blackout exceeds `toleratedForwardClockJump = maxOffset / 2` (e.g., >125 ms for a 250 ms `MaxOffset`), CockroachDB's jump monitor (`hlc.go:396–405`) detects a forward wall-clock jump on the very next tick and **terminates the node with `Fatalf`**—which is the *correct* fail-safe action because leases held by the paused VM may have already expired on peers!
  2. **Host-skew discontinuity across destination host:** Even when `kvmclock` maintains guest monotonicity across migration, the destination physical host's NTP/PTP clock can differ from the source host's clock, injecting a step or sudden slew rate change in `CLOCK_REALTIME` and invalidating cached PHC anchors (`fbclock` returns `FBCLOCK_E_DATA_STALE` or `FBCLOCK_E_PHC_IN_THE_PAST`).
  3. **`CLOCK_MONOTONIC` vs. `CLOCK_BOOTTIME` discrepancy:** Across ACPI S3 suspend or VM pause-to-disk, `CLOCK_MONOTONIC` freezes while real time (and `CLOCK_BOOTTIME`) advances—meaning a lease TTL tracked with `CLOCK_MONOTONIC` (or Rust's `std::time::Instant` on Linux!) **fails to count pause/suspend duration and can erroneously treat an expired distributed lease as still valid!**

---

### 5. Epistemic Temporal and Timescale Type Systems

*Basis: source (`rust-lang/rust` `library/std/src/time.rs`, `nyx-space/hifitime` `src/timescale/mod.rs`, `cockroachdb/cockroach` `pkg/util/hlc/timestamp.go`, `facebook/time/fbclock/fbclock.h`) + execution (Probe 2B) + derived*

#### 5.1 Lessons and Remaining Type Gaps in Existing Libraries

1. **`rust-lang/rust` (`b0b600668bb9b4a897e2299b0a44289d42276545`, `library/std/src/time.rs`):**
   - **What it gets right:** Separates monotonic `Instant` (`time.rs:156`) from non-monotonic wall `SystemTime` (`time.rs:248`), forcing `SystemTime::duration_since` to return `Result<Duration, SystemTimeError>` (`time.rs:605–620`) so callers cannot assume wall clocks never step backward.
   - **Three critical type-level gaps documented in source:**
     - *Silent zero-saturation masking argument-swap bugs (`time.rs:134–146, 289–316, 456–473`):* Because rare hardware, virtualization, and OS bugs broke `CLOCK_MONOTONIC` monotonicity in the field (causing older Rust versions to panic), `Instant::duration_since`, `elapsed()`, and `Sub<Instant>` now silently saturate to `Duration::ZERO` (`checked_duration_since(earlier).unwrap_or_default()`), masking logic bugs where callers accidentally compute `earlier - later`!
     - *Unspecified suspend behavior (`time.rs:56–57, 111–119`):* `Instant` maps to `CLOCK_MONOTONIC` on Linux (pauses during suspend) and `CLOCK_UPTIME_RAW` on Darwin, so it **cannot** soundly guard distributed lease timeouts across VM/host suspend unless explicitly switched to `CLOCK_BOOTTIME`.
     - *No timescale or locality indexing:* Neither `Instant` nor `SystemTime` prevents serializing a host-local `Instant` or subtracting `SystemTime` values read from two different machines or leap-smearing policies.
2. **`nyx-space/hifitime` (`e258220164f6f6a488e2e1d7083587a540990567`, `src/timescale/mod.rs:84–240` & `src/epoch/leap_seconds.rs`):**
   - Explicitly models `enum TimeScale { TAI, TT, ET, TDB, UTC, GPST, GST, BDT, QZSST, TCG, TCB, TL, TCL }`, canonicalizing internal arithmetic in continuous **TAI** (using exact 128-bit `(centuries: i16, nanoseconds: u64)` durations without floating-point precision loss), tagging `uses_leap_seconds()` as `true` exclusively for `TimeScale::UTC`, and validating embedded leap-second tables (42 entries through `37.0 s` on `2017-01-01`) via `Kani` verification harnesses (`src/kani_verif.rs`).
3. **CockroachDB `ClockTimestamp` (`timestamp.go:328–341`):** Demonstrates **provenance-carrying temporal newtypes**—distinguishing an arbitrary serializable `Timestamp` from a `ClockTimestamp` certified to have been observed on a live cluster HLC, so unvalidated timestamps cannot legally enter `Clock.Update`.

#### 5.2 Formal Type Discipline for Timescales, Locality, and Epistemic Intervals

A sound temporal type system for verified distributed and real-time software enforces four orthogonal invariants statically:

1. **Affine Space Separation (`Point<S, D>` vs. `Duration<S>`):** Points in time cannot be added (`Point + Point` is ill-typed); only `Point<S, D> - Point<S, D> -> SignedDuration<S>` and `Point<S, D> + Duration<S> -> Point<S, D>` are valid—and **only when both timescale `S` and locality domain `D` match**!
   - `Mono<HostId, ActiveOnly>` (`CLOCK_MONOTONIC`) cannot be subtracted from `Mono<HostId, IncludeSuspend>` (`CLOCK_BOOTTIME`) or from `Mono<OtherHostId, _>`.
   - `Point<Tai>` cannot be silently compared with `Point<UtcSmeared<Linear24h>>` without an explicit, error-returning conversion carrying a leap-second table / smear-bounds proof.
2. **Epistemic Uncertainty Interval Type (`EpistemicTime<S>`):**
   ```rust
   /// Invariant: earliest <= t_true <= latest (in timescale S, e.g. Tai)
   pub struct EpistemicTime<S> {
       earliest_ns: i128,
       latest_ns: i128,
       _scale: PhantomData<S>,
   }

   pub enum EpistemicOrder {
       CertainBefore, // self.latest_ns < other.earliest_ns
       CertainAfter,  // other.latest_ns < self.earliest_ns
       Uncertain,     // intervals overlap: ordering physically undecidable
   }
   ```
   - **Monotonic drift-widening law:** Advancing or extrapolating an interval across local monotonic elapsed time $\Delta t \ge 0$ with bounded oscillator frequency error $\rho$ (in ppb) must monotonically widen the bound:
     $$\text{widen}([e, l], \Delta t, \rho) = \left[e + \Delta t - \left\lceil \frac{\Delta t \cdot \rho}{10^9} \right\rceil,\; l + \Delta t + \left\lceil \frac{\Delta t \cdot \rho}{10^9} \right\rceil\right]$$
   - **Checked commit-wait witness:** A `CommitTimestamp<S>` token usable to release locks under external consistency can be minted *only* after observing a fresh `now: EpistemicTime<S>` satisfying `s.certain_before(now) == true` (i.e., `s.latest_ns < now.earliest_ns`).
3. **Why `EpistemicTime<S>` MUST NOT Implement `Ord` (Strict Interval Order Non-Transitivity):**
   - The relation $A <_{\text{cert}} B \iff A.\text{latest} < B.\text{earliest}$ is a **strict partial order** (irreflexive, asymmetric, transitive) and specifically a **strict interval order** (satisfying the Ferrers property: $(A <_{\text{cert}} B \land C <_{\text{cert}} D) \implies (A <_{\text{cert}} D \lor C <_{\text{cert}} B)$).
   - However, its incomparability relation $A \parallel B \iff \neg(A <_{\text{cert}} B) \land \neg(B <_{\text{cert}} A)$ (`EpistemicOrder::Uncertain`) is **NOT transitive**!
   - **Minimal witness (Probe 2B):** For $A = [0, 10], B = [8, 18], C = [15, 25]$, we have $A \parallel B$ (overlap $[8, 10]$) and $B \parallel C$ (overlap $[15, 18]$), **yet $A <_{\text{cert}} C$** ($10 < 15$)!
   - **Concrete systems bug prevented:** Rust's `Ord` trait, C++'s `std::sort`/`std::map`, and Go's `slices.SortFunc` all require a **strict weak ordering** (whose equivalence/incomparability relation *must* be transitive). Returning `Ordering::Equal` for overlapping intervals breaks binary search, corrupts balanced trees (`BTreeMap`), and triggers UB/out-of-bounds memory corruption in C++ `std::sort`! Epistemic intervals therefore implement `PartialOrd` (returning `None` on overlap) or an explicit `epistemic_cmp() -> EpistemicOrder`, *never* `Ord`, and any total key order (e.g., MVCC version key ordering) must explicitly choose a deterministic tie-breaking projection (such as `(earliest_ns, latest_ns)` or HLC `(WallTime, Logical)`) while keeping epistemic happens-before distinct.

---

### 6. Executable Micro-Probes and Reproducible Counterexamples

*Basis: execution (Python 3 on Linux x86_64, `2026-11-19`)*

#### 6.1 Probe Script (`probe_pkg2_clocks.py`)

```python
#!/usr/bin/env python3
"""Executable micro-probes for TrueTime commit-wait, HLC uncertainty, PTP asymmetry,
Huygens cycle consistency, leap-second smear divergence, and epistemic interval orders."""
import math
import random


def probe_truetime_vs_hlc():
    print("=== Probe 2A: TrueTime Commit-Wait vs HLC Out-of-Band External Consistency ===")
    rng = random.Random(2026)
    eps = 4_000_000  # 4 ms half-width (ns), typical Spanner epsilon

    violations_full = 0
    for _ in range(10000):
        t1 = 10_000_000_000
        e1 = rng.randint(-eps, eps)
        e2 = rng.randint(-eps, eps)
        s1 = (t1 + e1) + eps
        t_done = s1 + eps - e1 + 1  # earliest instant where TT1.after(s1) is true
        s2 = (t_done + e2) + eps
        if not (s1 < s2):
            violations_full += 1

    e1_wc, e2_wc, t1_wc = +eps, -eps, 10_000_000_000
    s1_wc = t1_wc + e1_wc + eps
    s2_wc = (t1_wc + 2 * eps - 1) + e2_wc + eps  # commit-wait cut 1 ns short
    e1_breach = eps + 500
    s1_b = t1_wc + e1_breach + eps
    t_done_b = s1_b + eps - e1_breach + 1
    s2_b = t_done_b + (-eps - 500) + eps  # |e| exceeds eps by 500 ns
    print(f"  TrueTime full commit-wait (10,000 random skews, |e|<=4ms): violations={violations_full}/10000")
    print(f"  Minimal counterexample (wait cut 1ns short): s1={s1_wc}, s2={s2_wc} (s2 - s1 = {s2_wc - s1_wc} ns)")
    print(f"  Minimal counterexample (|e| exceeds eps by 500ns): s1={s1_b}, s2={s2_b} (s2 - s1 = {s2_b - s1_b} ns)")

    max_offset = 250_000_000
    t_real = 100_000_000_000
    hlc1 = (t_real + 100_000_000, 0)
    hlc2 = (t_real + 1_000_000 - 100_000_000, 0)
    uncert_limit = (hlc2[0] + max_offset, 0)
    print(f"  HLC (skew=200ms <= max_offset=250ms): T1_ts={hlc1[0]}, T2_ts={hlc2[0]} (T2-T1={(hlc2[0]-hlc1[0])/1e6:.1f}ms)")
    print(
        f"    Same-key read without uncertainty check stale={hlc2 < hlc1}; "
        f"caught by ReadWithinUncertaintyIntervalError={hlc2 < hlc1 <= uncert_limit}"
    )
    print(f"    Disjoint-key T2 write real-time timestamp inversion (hlc2 < hlc1)={hlc2 < hlc1}")


def probe_ptp_huygens_smear_and_intervals():
    print("\n=== Probe 2B: PTP Asymmetry, Huygens Cycle Closure, Leap Smear Divergence & Interval Order ===")
    true_offset, d_ms, d_sm = 12_345, 2_400, 1_600
    t1 = 1_000_000
    t2 = t1 + d_ms + true_offset
    t3 = t2 + 5_000
    t4 = t3 - true_offset + d_sm
    est_delay = ((t2 - t3) + (t4 - t1)) / 2.0
    est_offset = (t2 - t1) - est_delay
    print(
        f"  PTP asymmetry (d_ms={d_ms}ns, d_sm={d_sm}ns): true_offset={true_offset}ns, "
        f"est_delay={est_delay:.1f}ns, est_offset={est_offset:.1f}ns, bias={est_offset-true_offset:+.1f}ns "
        f"(exact formula (d_ms-d_sm)/2 = {(d_ms-d_sm)/2:+.1f}ns)"
    )

    true_x = [0.0, 100.0, -50.0, 200.0, -120.0]
    n = len(true_x)
    meas = {(i, j): (true_x[j] - true_x[i]) + (800.0 if (i, j) == (0, 1) else 0.0)
            for i in range(n) for j in range(i + 1, n)}
    tri_residuals = [meas[(0, 1)] + meas[(1, k)] - meas[(0, k)] for k in range(2, n)]
    two_hop_ests = [meas[(0, k)] - meas[(1, k)] for k in range(2, n)]
    all_ests_01 = sorted([meas[(0, 1)]] + two_hop_ests)
    median_01 = all_ests_01[len(all_ests_01) // 2]
    avg_1_2hop = (meas[(0, 1)] + sum(two_hop_ests)) / (1 + len(two_hop_ests))
    print(
        f"  Huygens K_5 triangle closure on biased link (0,1) (+800ns): "
        f"triangle residuals={tri_residuals} ns; 1+2-hop avg error={avg_1_2hop - (true_x[1]-true_x[0]):+.1f}ns; "
        f"cycle-median error={median_01 - (true_x[1]-true_x[0]):+.1f}ns"
    )

    def off_step(t): return 1.0 if t >= 0.0 else 0.0
    def off_lin24(t): return 0.0 if t <= -43200.0 else (1.0 if t >= 43200.0 else (t + 43200.0) / 86400.0)
    def off_cos24(t): return 0.0 if t <= -43200.0 else (1.0 if t >= 43200.0 else 0.5 * (1.0 - math.cos(math.pi * (t + 43200.0) / 86400.0)))
    def off_lin20(t): return 0.0 if t <= -36000.0 else (1.0 if t >= 36000.0 else (t + 36000.0) / 72000.0)
    def off_fbclock_post(t): return 0.0 if t <= 0.0 else (1.0 if t >= 62500.0 else t / 62500.0)

    samples = [float(s) for s in range(-43200, 62501, 10)] + [-0.001, 0.0, 0.001]
    print("  Cross-domain leap-second smear peak divergences:")
    for name, f1, f2 in [
        ("Step-UTC vs 24h-linear", off_step, off_lin24),
        ("24h-linear vs 24h-cosine", off_lin24, off_cos24),
        ("24h-linear vs 20h-linear", off_lin24, off_lin20),
        ("24h-linear vs post-62500s (fbclock v2)", off_lin24, off_fbclock_post),
    ]:
        peak_val, peak_t = max((abs(f1(t) - f2(t)), t) for t in samples)
        print(f"    {name:40s}: peak={peak_val*1000:6.2f} ms at t={peak_t:+.0f}s")

    def cert_before(a, b): return a[1] < b[0]
    def uncertain(a, b): return not cert_before(a, b) and not cert_before(b, a)
    A, B, C = (0, 10), (8, 18), (15, 25)
    print(
        f"  Interval order witness A={A}, B={B}, C={C}: "
        f"A||B={uncertain(A,B)}, B||C={uncertain(B,C)}, yet A<_cert C={cert_before(A,C)} (incomparability non-transitive!)"
    )

    a, b, delta = 0.0, 100.0, 100.0
    for _ in range(5):
        a, b = (a + (a - delta) + b) / 3.0, (a + b + (b + delta)) / 3.0
    print(f"  Byzantine CNV counterexample (n=3, f=1, n=3f): after 5 rounds, A={a:.1f}, B={b:.1f}, |B-A|={b-a:.1f} (never converges!)")
    a, b, c = 0.0, 100.0, 50.0
    for _ in range(5):
        a, b, c = (a + b + c + (a - delta)) / 4.0, (a + b + c + (b + delta)) / 4.0, (a + b + c + c) / 4.0
    print(f"  Byzantine CNV convergence (n=4, f=1, n=3f+1): after 5 rounds, spread max-min={max(a,b,c)-min(a,b,c):.2f} (contracting!)")


if __name__ == "__main__":
    probe_truetime_vs_hlc()
    probe_ptp_huygens_smear_and_intervals()
```

#### 6.2 Observed Output

```text
=== Probe 2A: TrueTime Commit-Wait vs HLC Out-of-Band External Consistency ===
  TrueTime full commit-wait (10,000 random skews, |e|<=4ms): violations=0/10000
  Minimal counterexample (wait cut 1ns short): s1=10008000000, s2=10007999999 (s2 - s1 = -1 ns)
  Minimal counterexample (|e| exceeds eps by 500ns): s1=10008000500, s2=10007999501 (s2 - s1 = -999 ns)
  HLC (skew=200ms <= max_offset=250ms): T1_ts=100100000000, T2_ts=99901000000 (T2-T1=-199.0ms)
    Same-key read without uncertainty check stale=True; caught by ReadWithinUncertaintyIntervalError=True
    Disjoint-key T2 write real-time timestamp inversion (hlc2 < hlc1)=True

=== Probe 2B: PTP Asymmetry, Huygens Cycle Closure, Leap Smear Divergence & Interval Order ===
  PTP asymmetry (d_ms=2400ns, d_sm=1600ns): true_offset=12345ns, est_delay=2000.0ns, est_offset=12745.0ns, bias=+400.0ns (exact formula (d_ms-d_sm)/2 = +400.0ns)
  Huygens K_5 triangle closure on biased link (0,1) (+800ns): triangle residuals=[800.0, 800.0, 800.0] ns; 1+2-hop avg error=+200.0ns; cycle-median error=+0.0ns
  Cross-domain leap-second smear peak divergences:
    Step-UTC vs 24h-linear                  : peak=500.00 ms at t=+0s
    24h-linear vs 24h-cosine                : peak=105.26 ms at t=-24220s
    24h-linear vs 20h-linear                : peak= 83.33 ms at t=+36000s
    24h-linear vs post-62500s (fbclock v2)  : peak=500.00 ms at t=+0s
  Interval order witness A=(0, 10), B=(8, 18), C=(15, 25): A||B=True, B||C=True, yet A<_cert C=True (incomparability non-transitive!)
  Byzantine CNV counterexample (n=3, f=1, n=3f): after 5 rounds, A=0.0, B=100.0, |B-A|=100.0 (never converges!)
  Byzantine CNV convergence (n=4, f=1, n=3f+1): after 5 rounds, spread max-min=66.70 (contracting!)
```

## Boundaries

- **GNSS jamming/spoofing and cryptographic PTP authentication (NTS / IEEE 1588-2019 Prong A/B `AUTHENTICATION` TLV / MACsec) — `not examined`:** While Byzantine clock bounds ($n \ge 3f + 1$ oral vs. $n \ge 2f + 1$ signed) are documented, physical-layer GNSS spoofing detection, Network Time Security (RFC 8915), and IEEE 1588-2019 Annex P security mechanisms were not audited in source.
- **White Rabbit (Sub-Nanosecond Synchronous Ethernet + Phase-Tracking PTP) and Relativistic Coordinate Scales (TCG/TCB/TCL) — `not examined`:** Sub-nanosecond fiber-asymmetry calibration via White Rabbit (IEEE 1588-2019 High Accuracy Profile) and relativistic gravitational redshift corrections (referenced in `hifitime`'s `TimeScale::TCG`/`TCB`/`TCL`) are outside datacenter LAN/WAN scope.
- **KVM live-migration behavior on ARM64 (`CNTVCT_EL0` / `CNTVOFF_EL2`) and Windows Hyper-V (`HV_X64_MSR_TIME_REF_COUNT`) — `not examined`:** Source inspection of hypervisor clocks was restricted to x86 Linux `kvmclock` (`pvclock-abi.h`, `kvmclock.c`).
- **Statistical tail risk of probabilistic WOU bounds (`fbclock` 6-9s claim) — `unknown`:** `facebook/time/fbclock/README.md:9` states a *"6-9s guarantee"* that true time lies within `[earliest, latest]`; empirically verifying the true tail exceedance probability under correlated switch failures or thermal crystal shocks requires live fleet telemetry and cannot be deduced from the C client source alone.
- **Stronger claims NOT established (do not over-extrapolate):**
  - *Known not to apply:* CockroachDB HLC without commit-wait does **not** guarantee full strict serializability (external consistency) for causally disconnected disjoint-key writes, and CockroachDB's own `hlc.go:332–335` explicitly marks even serializability under `> MaxOffset` clock skew as unverified conjecture.
  - *Known not to apply:* Collapsing an epistemic interval `[earliest, latest]` to its arithmetic midpoint (`fbclock_truetime_midpoint_ns`) does **not** preserve happens-before soundness, and implementing total-order `Ord` on uncertainty intervals violates strict weak ordering.
  - *Known not to apply:* Linux `CLOCK_TAI` does **not** automatically equal TAI on a freshly booted kernel—it equals `CLOCK_REALTIME` (`tai = 0`) until `ntpd`/`chronyd`/`phc2sys` explicitly sets the 37-second offset via `adjtimex(ADJ_TAI)`.

## Evidence

### Inspected Upstream Source Revisions (Observed `2026-11-19`)

1. **`cockroachdb/cockroach`** — commit `d30c905fff79ef825adc96bcc647f1872a90f2ff`:
   - `pkg/util/hlc/hlc.go` (lines 38–92, 224–451, 465–590): `Clock` struct (`maxOffset`, `toleratedOffset`, `wallTimeUpperBound`), `toleratedForwardClockJump = c.maxOffset / 2`, `StartMonitoringForwardClockJumps`, `MaxOffset()` / `ToleratedOffset()` caveats, `checkPhysicalClock` (`Fatalf` on forward jump, warn on backward $> \text{maxOffset}/10$), `NowAsClockTimestamp`, `enforceWallTimeWithinBoundLocked`, `Update`, `UpdateAndCheckMaxOffset`, `RefreshHLCUpperBound`.
   - `pkg/util/hlc/timestamp.go` (lines 20–62, 328–348): `Timestamp` lexicographic `Less`/`Compare`, capability newtype `ClockTimestamp` and `UnsafeToClockTimestamp`.
   - `pkg/kv/kvpb/errors.proto` (lines 114–137): `message ReadWithinUncertaintyIntervalError` (`read_timestamp`, `local_uncertainty_limit`, `global_uncertainty_limit`, `value_timestamp`).
2. **`facebook/time`** — commit `62fc415c683e157653af71e4ac34216eedaf5879`:
   - `fbclock/fbclock.h` (lines 51–275, 324–416): error codes (`FBCLOCK_E_WOU_TOO_BIG`, `FBCLOCK_E_PHC_IN_THE_PAST`, `FBCLOCK_E_DATA_STALE`), `UTC_TAI_OFFSET_NS = -37e9`, `FBCLOCK_MAX_EXTRAPOLATION_NS = 10s`, `fbclock_shmsection`/`fbclock_data_section` (`alignas(64) atomic_uint64 seq`), `fbclock_truetime`, anti-midpoint specification on `fbclock_truetime_midpoint_ns`.
   - `fbclock/fbclock.c` (lines 48–92, 114–225, 592–820, 945–1009): layout `static_assert`s, `SMEAR_DURATION = 62500`, seqlock acquire/release fences, `fbclock_window_of_uncertainty`, signed `coef_ppb` division in `fbclock_calculate_time_v2`, pure-TAI non-smearing `fbclock_gettime_v3` (line 801), `fbclock_apply_smear`.
   - `fbclock/README.md` (lines 1–53): WOU `M`, `W`, `Drift` model and 6-9s design goal.
3. **`richardcochran/linuxptp`** — commit `227bbd4715bf4cb735be4947e987032f41457585`:
   - `tsproc.c` (lines 27–48, 124–228): `get_raw_delay` (`((t2 - t3) * rr + (t4 - t1)) / 2`), `tsproc_update_offset` (`(t2 - t1) - delay`).
   - `clock.c` (lines 129–136, 932–974): `master_offset`, `path_delay`, `PTP_TIMESCALE` TAI-to-UTC `utc_offset` conversion.
4. **`torvalds/linux`** — commit `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`:
   - `include/uapi/linux/time.h` (lines 49–80): `CLOCK_REALTIME (0)`, `CLOCK_MONOTONIC (1)`, `CLOCK_MONOTONIC_RAW (4)`, `CLOCK_BOOTTIME (7)`, `CLOCK_TAI (11)`, `CLOCK_AUX (16..23)`.
   - `include/uapi/linux/timex.h` (lines 139–205): `ADJ_TAI`, `STA_INS`, `STA_DEL`, `TIME_OK..TIME_BAD`.
   - `arch/x86/include/asm/pvclock-abi.h` (lines 26–47): 32-byte `struct pvclock_vcpu_time_info`, `PVCLOCK_TSC_STABLE_BIT`, `PVCLOCK_GUEST_STOPPED`.
   - `arch/x86/kernel/kvmclock.c` (lines 75–171, 264–372): `kvm_clock_get_cycles_snapshot`, `kvm_check_and_clear_guest_paused`, `VDSO_CLOCKMODE_PVCLOCK` stability gating.
5. **`rust-lang/rust`** — commit `b0b600668bb9b4a897e2299b0a44289d42276545`:
   - `library/std/src/time.rs` (lines 44–270, 289–390, 456–620): `Instant` monotonicity workaround (zero saturation in `duration_since`/`Sub`), platform syscall table (`CLOCK_MONOTONIC`, `CLOCK_UPTIME_RAW`, `QueryPerformanceCounter`), unspecified suspend behavior, `SystemTime` and `SystemTimeError`.
6. **`nyx-space/hifitime`** — commit `e258220164f6f6a488e2e1d7083587a540990567`:
   - `src/timescale/mod.rs` (lines 84–240): `enum TimeScale`, `uses_leap_seconds()`, canonical TAI prime-epoch offsets.
   - `src/epoch/leap_seconds.rs` (lines 29–91): `LATEST_LEAP_SECONDS` 42-entry table terminating at `37.0 s` on `2017-01-01`.

### Primary Standards & Peer-Reviewed Literature

- J. Lundelius & N. Lynch, *"An Upper and Lower Bound for Clock Synchronization"*, Information and Control 62(2–3), 1984, `DOI: 10.1016/s0019-9958(84)80033-9`.
- L. Lamport & P. M. Melliar-Smith, *"Synchronizing Clocks in the Presence of Faults"*, Journal of the ACM 32(1), 1985, `DOI: 10.1145/2455.2457`.
- D. Dolev, J. Y. Halpern, H. R. Strong, *"On the Possibility and Impossibility of Achieving Clock Synchronization"*, JCSS 32(2), 1986, `DOI: 10.1016/0022-0000(86)90028-0`.
- J. C. Corbett et al., *"Spanner: Google's Globally-Distributed Database"*, USENIX OSDI 2012 & ACM TOCS 31(3), 2013, `DOI: 10.1145/2491245`.
- S. S. Kulkarni, M. Demirbas, D. Madeppa, B. Avva, M. Leone, *"Logical Physical Clocks"*, OPODIS 2014, `DOI: 10.1007/978-3-319-14472-6_2`.
- Y. Geng, S. Liu, Z. Yin, A. Naik, B. Prabhakar, M. Rosenblum, A. Vahdat, *"Exploiting a Natural Network Effect for Scalable, Fine-grained Clock Synchronization"*, USENIX NSDI 2018.
- IEEE Std 1588-2019 (PTPv2.1); IEEE Std 802.1Qbv-2015 / IEEE Std 802.1Q-2022 (TSN Scheduled Traffic); IEEE Std 1003.1 (POSIX).
- BIPM 27th CGPM Resolution 4 (November 2022) & 28th CGPM Resolution 5 (October 13–15, 2026, continuous UTC effective May 20, 2027 with 3,600 s $|UT1 - UTC|$ bound).

### Execution Provenance

- Ran `python3 /tmp/probe_pkg2_clocks.py` on `2026-11-19` (exit code `0`); full script and deterministic stdout preserved verbatim in Section 6.

## Revalidation

Use the following targeted checks to determine whether the key findings still hold on newer upstream revisions or deployments:

1. **Check CockroachDB HLC dynamic `MaxOffset` or commit-wait changes (`cockroachdb/cockroach`):**
   - Diff `pkg/util/hlc/hlc.go` (specifically `toleratedForwardClockJump`, `MaxOffset`, `UpdateAndCheckMaxOffset`, and the `TODO` on dynamic `maxOffset` at line 45) against `d30c905fff79ef825adc96bcc647f1872a90f2ff`.
2. **Check Meta `fbclock` v3 rollout & smearing policy (`facebook/time`):**
   - Diff `fbclock/fbclock.h` and `fbclock/fbclock.c` against `62fc415c683e157653af71e4ac34216eedaf5879` to confirm whether `FBCLOCK_VERSION_DEFAULT` has switched from `v2` to `v3` and whether `fbclock_gettime_v3` remains pure TAI without smearing.
3. **Check Rust `std::time::Instant` panic/saturation policy (`rust-lang/rust`):**
   - Diff `library/std/src/time.rs` against `b0b600668bb9b4a897e2299b0a44289d42276545` to see if `Instant::duration_since` reintroduced panics on reversed instants or added explicit `CLOCK_BOOTTIME` support.
4. **Check host `CLOCK_TAI` configuration before deploying TAI-anchored protocols:**
   - Run `adjtimex --print` (or inspect `struct timex.tai` via `adjtimex(2)`) on target Linux hosts and confirm `tai == 37` (or the current IERS offset) rather than uninitialized `0`.
5. **Rerun inline micro-probes:**
   - Save Section 6.1 to `/tmp/probe_pkg2_clocks.py` and run `python3 /tmp/probe_pkg2_clocks.py`; verify exact reproduction of TrueTime 0/10,000 violations vs. `-1 ns` and `-999 ns` counterexamples, PTP `+400.0 ns` asymmetry bias, Huygens `0.0 ns` cycle-median recovery, `500.00 ms` / `105.26 ms` smear divergences, interval-order non-transitivity, and $n=3$ vs. $n=4$ Byzantine CNV behavior.
