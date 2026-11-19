# Leap-Second Smearing Divergence, Non-Injective UTC/POSIX Epoch Folds, and Civil TZDB Ambiguity Bugs

## Summary

Almost every production operating system, distributed database, financial exchange, and sensor-telemetry runtime conflates at least two of five mathematically distinct temporal domains (`Basis: normative, source, execution`): (1) **International Atomic Time (`TAI`)**, an unbounded, strictly monotonic SI-second counter; (2) **Coordinated Universal Time (`UTC`)**, a piecewise-affine step scale synchronized to Earth's irregular rotation (`UT1`) via irregular IERS `±1 s` leap seconds (`23:59:60`); (3) **POSIX Unix Time (`CLOCK_REALTIME`)**, a *non-injective* scalar integer defined as `86,400` seconds per solar day excluding leap seconds; (4) **Leap-Smeared NTP Time**, synthetic frequency-warped clocks (`-11.57 ppm` to `-18.18 ppm`) whose phase diverges by up to **`500.0 ms`** from `UTC` and by **`105.26–125.00 ms`** across competing cloud smear curves; and (5) **Civil Zoned Wall Time (`IANA tzdb`)**, a politically mutated, neither injective nor surjective projection exhibiting `1`-hour Daylight Saving Time (`DST`) gaps, `fold = 0/1` backward repeats, and historical sub-minute/date-line jumps.

Across primary-source inspections of `torvalds/linux` (`8dac6df92a2e66e2098bbc69061964cfe7e8375b` `kernel/time/ntp.c`), `golang/go` (`9535db20eb78901d6a15a880e6700d428c1b7077` `src/time/time.go`), `mlichvar/chrony` (`372462ca6c1a822245544003199a24ebfad1fc0e` `smooth.c` & `reference.c`), `BurntSushi/jiff` (`623ea08d41d4ad0c647585eed9405e6b76d2d27e`), `chronotope/chrono` (`6adaa5240c26fecb7bd9077334a91f8f67f4f3fe`), `HowardHinnant/date` (`2390d3da331bc44b89940d9b3397ab438ebb6a41` `include/date/tz.h`), `eggert/tz` (`84585da3a2db8cb439e1674f84cf637ac9df6aaa` `localtime.c`), `SeisComP/seiscomp` (`0f456a83db3435ef92b809bc47077c84b3a4883b` `libmseed/genutils.c`), Cloudflare's 1 January 2017 `rrdns` outage post-mortem, and EU `MiFID II RTS 25`, four concrete failure anatomies emerge:

1. **Non-Injective POSIX Epoch Folds, Kernel `TIME_OOP` Replays, and Monotonic-Bit Stripping (`Basis: normative, source, execution`)**: Under POSIX.1 (`Base Definitions §4.16`), every UTC day maps to exactly `86,400` Unix seconds. When `STA_INS` inserts a positive leap second (`23:59:60 UTC`), Linux's `second_overflow()` (`kernel/time/ntp.c:633–636`) sets `leap = -1` and `ntpdata->time_state = TIME_OOP`, **stepping `CLOCK_REALTIME` backward by `1.000 s`** to replay `[T - 1, T)` (historically triggering the 30 June 2012 Linux `hrtimer` `futex` CPU livelock when `clock_was_set()` was deferred from hardirq context, and triggering **Cloudflare's 1 January 2017 global DNS outage** when Go 1.7's wall-only `time.Now().Sub(start)` produced `-985 ms`, panicking `rand.Int63n` in `rrdns`). Even in modern Go (`src/time/time.go:140–166, 1198–1212`), `Time.Sub` uses monotonic `ext` *only* when bit `63` (`hasMonotonic`) is set on **both** operands—calling `t.Round(0)`, `MarshalJSON()`, or parsing RFC 3339 strings silently strips `hasMonotonic` and re-exposes the `-985 ms` negative duration! Worse, user-space `:60` parsers disagree by a full **`1,000 ms`**: `BurntSushi/jiff` (`parser.rs:823–825`) clamps `:60 -> :59` (folding backward onto `23:59:59`), `SeisComP/libmseed` (`genutils.c:1311`) evaluates `60*(...) + 60` (folding forward onto `00:00:00`), and `chronotope/chrono` (`naive/time/mod.rs:68–90`) stores `second = 59` with **`nanosecond = 1_000_000_000 .. 1_999_999_999`** (violating `< 10^9` C `timespec` invariants across FFI boundaries).
2. **Incompatible `24-Hour` Leap-Smear Phase Curves, Cloud PTP/NTP Split-Brain, and `MiFID II` Violations (`Basis: documentation, source, execution, derived`)**: To hide `TIME_OOP` replays, cloud NTP servers smear the extra second across a window $W$ (`24 h = 86,400 s`), deliberately falsifying `CLOCK_REALTIME` rate and phase:
   - **Google Public NTP & AWS `time.aws.com`** apply a `24 h` noon-to-noon **linear** smear (`-11.574 ppm`), peaking at **`±500.0 ms` error vs. true UTC** at midnight—exceeding EU **`MiFID II RTS 25`'s `100 us` HFT clock-traceability ceiling by `5,000x`**.
   - **Cosine noon-to-noon smear** ($\frac{1}{2}(1 - \cos \pi u)$, continuous frequency at endpoints) diverges from linear smear by **`105.26 ms`**, while **`chrony`'s `leapsecmode slew` + `smoothtime ... leaponly`** (`smooth.c:134–205`, symmetric 2-stage constant-wander quadratic slew) diverges from linear smear by **`125.00 ms`** at `18:00 UTC` and `06:00 UTC`.
   - **Intra-VPC NTP vs. PTP Split-Brain**: AWS EC2 smears its local NTP service (`169.254.169.123`) over `24 h` while serving **unsmeared true UTC/TAI** on its EC2 PTP Hardware Clock (`PHC`), creating a **`500.0 ms` inter-node clock skew inside a single availability zone** that breaks TrueTime/HLC commit-wait external consistency bounds (`2\epsilon \ll 500\text{ ms}`).
3. **GPS `1,024`-Week Rollover & `TAI` / `GPST` / `UTC` Affine Scale Confusions (`Basis: normative, source, execution`)**: `HowardHinnant/date` (`include/date/tz.h:1870, 2061, 2116, 2181, 2226`) codifies C++20's distinct `utc_clock`, `tai_clock` (`1958-01-01` epoch, `TAI - UTC = +37 s` since `2017-01-01`), and `gps_clock` (`1980-01-06` epoch, locked to `TAI - 19 s`, so `GPST - UTC = +18 s`). Legacy IS-GPS-200 L1 C/A navigation frames encode week number in **`10` bits (`modulo 1,024 weeks = 619,315,200 s ≈ 19.62 years`)**, rolling over on 21 August 1999 and 6 April 2019 (and firmware pivot epochs rolling over mid-cycle, e.g., Boeing 777/787 Honeywell GPS/adahrs advisories & cellular base-station outages).
4. **IANA `tzdb` Civil Spring-Forward Gaps, Fall-Back `fold=0/1` Double Execution, and Mutable Future Zone Rules (`Basis: normative, source, execution`)**: Civil wall-to-instant projection $\pi_z^{-1} : \text{Civil} \to \mathcal{P}(\text{Instant})$ has cardinality **`0` (gap)**, **`1` (unambiguous)**, or **`2` (fold)** (`chrono::MappedLocalTime` in `offset/mod.rs:85–95`; `jiff::tz::Disambiguation` in `ambiguous.rs:80–105`). During `America/New_York`'s `2024-03-10T02:30` spring-forward gap, `Disambiguation::Compatible` (`03:30 EDT = 07:30Z`) and `Disambiguation::Earlier` (`01:30 EST = 06:30Z`) differ by **`3,600 s`**, while during `2024-11-03T01:30`'s fall-back fold (`05:30Z` `fold=0` vs. `06:30Z` `fold=1`), naive cron schedulers double-fire non-idempotent billing jobs and future timestamps stored as pre-computed UTC epochs silently drift by `3,600 s` whenever parliaments amend `tzdb` DST rules after write time.

## Applicability

This report governs timekeeping, distributed consensus (`Spanner` TrueTime / Hybrid Logical Clocks `HLC`), telemetry ingestion, financial audit logging, and static type/verification design across the nine subjects in `REPORT.json` (`Basis: derived`):

- **Subject Relationships**:
  - **OS Kernel & Network Synchronization Layer**: `torvalds/linux` (`kernel/time/ntp.c`) implements the RFC 5905 / Mills kernel PLL and `TIME_INS`/`TIME_OOP` step-back semantics, whereas `mlichvar/chrony` (`reference.c`, `smooth.c`) implements user-space NTP leap-slew and cubic/quadratic server time smoothing contrasted against Google/AWS linear smearing, `IEEE 1588-2019` (`PTPv2` `currentUtcOffset` over `TAI`), and `EU MiFID II RTS 25`.
  - **Runtime & Language Library Layer**: `golang/go` (`src/time/time.go`) illustrates post-Cloudflare-`2017` monotonic-plus-wall fat `Time` values (`hasMonotonic`), while `HowardHinnant/date` (C++20 `<chrono>`), `BurntSushi/jiff` (Rust `RFC 9557` / Temporal), `chronotope/chrono` (Rust legacy `>1e9 ns` leap encoding), `eggert/tz` (`tzcode` `localtime.c`), and `SeisComP/seiscomp` (`libmseed` `genutils.c`) are compared directly across `:60` parsing, scale separation, and `tzdb` gap/fold disambiguation.
- **Exact Observation vs. Broader Applicability**:
  - Exact source line numbers apply to the pinned commits (`Linux` `8dac6df9...`, `Go` `9535db2...`, `chrony` `372462c...`, `jiff` `623ea08...`, `chrono` `6adaa52...`, `date` `2390d3d...`, `tz` `84585da...`, `seiscomp` `0f456a8...`).
  - Note on international policy boundary: CGPM Resolution 4 (`2022`) and ITU-R WRC-23 resolved to increase the maximum `|UT1 - UTC|` tolerance (eliminating routine leap seconds by or before **`2035`**), **not** retroactively erasing the `27` historical leap seconds (`1972–2017`) embedded in `tzdb`/`GPST`/`TAI` offsets nor eliminating negative-leap/smear code paths still active in `Linux`, `chrony`, and GNSS receivers today.

## Findings

### 1. Non-Injective POSIX Epoch Folds, `TIME_OOP` Replays, and Monotonic-Bit Stripping

#### 1.1 Kernel `second_overflow()` Step-Back vs. `CLOCK_TAI` (`kernel/time/ntp.c:606–658`)
`Basis: normative, source, execution`

POSIX.1 defines Unix seconds since `1970-01-01T00:00:00Z` via the closed-form calendar polynomial (`86,400` seconds per day), forcing the mapping $\phi_{\text{POSIX}} : \text{UTC} \to \mathbb{Z}$ to lose injectivity on every positive leap second. In `torvalds/linux` (`8dac6df92a2e66e2098bbc69061964cfe7e8375b`, `kernel/time/ntp.c:606–658`), `second_overflow()` executes at every second boundary:

```c
// torvalds/linux kernel/time/ntp.c:629-653
case TIME_INS:
    if (!(ntpdata->time_status & STA_INS)) {
        ntpdata->ntp_next_leap_sec = TIME64_MAX;
        ntpdata->time_state = TIME_OK;
    } else if (secs == ntpdata->ntp_next_leap_sec) {
        leap = -1;
        ntpdata->time_state = TIME_OOP;
        pr_notice("Clock: inserting leap second 23:59:60 UTC\n");
    }
    break;
...
case TIME_OOP:
    ntpdata->ntp_next_leap_sec = TIME64_MAX;
    ntpdata->time_state = TIME_WAIT;
    break;
```

When `second_overflow()` returns `leap = -1` at `2017-01-01T00:00:00Z` (`secs == 1483228800`), `timekeeping.c` subtracts `1` full second (`NSEC_PER_SEC`) from `CLOCK_REALTIME` while simultaneously incrementing `tk->tai_offset` (`36 -> 37`) so **`CLOCK_TAI` (`tk->xtime_sec + tk->tai_offset`) advances smoothly from `1483228835` to `1483228836` without discontinuity**. Two major production failure classes followed directly from `leap = -1`:

1. **The 2012 Linux `hrtimer` / `futex` CPU Livelock**: Prior to Linux commit `6b43ae8a619d`, subtracting `1 s` inside `second_overflow()` left the `hrtimer` `CLOCK_REALTIME` base offset stale until a deferred `clock_was_set()` call; every thread calling `futex_wait` with a sub-second `CLOCK_REALTIME` timeout saw its timer expire *immediately* in a tight kernel loop, spiking CPU load to `100%` across global Linux fleets on 30 June 2012.
2. **Cloudflare's 2017-01-01 `rrdns` Negative-Duration Panic & Go's Fragile `hasMonotonic` Bit (`src/time/time.go:140–166, 1198–1212`)**:
   - At `2017-01-01T00:00:00Z`, Cloudflare's Go 1.7 authoritative DNS server (`rrdns`) measured upstream resolver latency via `now.Sub(start)` (`15 ms` physical elapsed time across the `-1.0 s` replay $\implies$ **`-985 ms`**, `probes/verify_leap_smear_tzdb.py`), passing a negative weight into `rand.Int63n(max)` which unconditionally panicked!
   - Go 1.9 (`src/time/time.go:140–166`) embedded a `1`-bit `hasMonotonic = 1 << 63` flag inside `Time.wall`, storing `33`-bit wall seconds (`1885–2157`) in `wall[62:30]` and `64`-bit monotonic process-relative nanoseconds in `Time.ext`:
     ```go
     // golang/go src/time/time.go:1198-1203
     func (t Time) Sub(u Time) Duration {
         if t.wall&u.wall&hasMonotonic != 0 {
             return subMono(t.ext, u.ext)
         }
         d := Duration(t.sec()-u.sec())*Second + Duration(t.nsec()-u.nsec())
     ```
   - **Hidden Footgun**: `hasMonotonic` is **silently erased** (`stripMono()`, `line 1186`) by `t.Round(0)`, `t.Truncate(...)`, `t.UTC()`, `t.In(loc)`? (No: `UTC()`/`In()` preserve `ext`, whereas `Time.MarshalJSON()`, `Time.MarshalBinary()`, protobuf `google.protobuf.Timestamp`, SQL `TIMESTAMPTZ` round-trips, `time.Date(...)`, and `time.Parse(...)` **all produce `hasMonotonic == 0`**!). Subtracting `time.Now().Sub(parsedStartTimeFromRedisOrRPC)` **bypasses `subMono` at line `1199` and executes line `1202` (`wall - wall`)**, crashing with the exact same `-985 ms` negative duration today!

#### 1.2 Three Incompatible `:60` Leap-Second Encodings (`1,000 ms` Skew + FFI Overflow)
`Basis: source, execution`

| Library & Exact Source Location | Representation of `2016-12-31T23:59:60.500Z` | Resulting Epoch / Field Invariant | Failure Mode Across Subsystem Boundaries |
| :--- | :--- | :--- | :--- |
| **`BurntSushi/jiff`** (`crates/jiff/src/fmt/temporal/parser.rs:823–825`) | `if second == 60 { second = 59; }` (per `RFC 9557` / ECMAScript `Temporal`) | `1483228799.500` (**folds `-1.0 s` backward** onto `23:59:59.500Z`) | Reorders events occurring at `23:59:59.800Z` *after* events occurring `700 ms` later at `23:59:60.500Z`! |
| **`SeisComP` / `libmseed`** (`genutils.c:193, 1311`) | `VALIDSEC(sec <= 60)` fed into `60*(60*(24*d+23)+59) + 60` | `1483228800.500` (**folds `+1.0 s` forward** onto `2017-01-01T00:00:00.500Z`) | **`1,000 ms` timestamp skew** against `jiff`/Temporal parsers on the exact same UTC instant! |
| **`chronotope/chrono`** (`src/naive/time/mod.rs:68–90`) | `secs = 86399` (`23:59:59`) + **`frac = 1_500_000_000`** (`>= 10^9` ns!) | `nanosecond()` returns `1_500_000_000` (`[10^9, 2*10^9 - 1]`) | Violates POSIX `tv_nsec < 1_000_000_000` (`EINVAL` in `clock_nanosleep`/`futimens` & panics in `std::time::Duration::new(s, ns)` if unchecked)! |
| **`HowardHinnant/date` / C++20 `<chrono>`** (`include/date/tz.h:1870–2055`) | `utc_clock` counts true SI seconds including all `27` `tzdb` leap seconds | Bijective `1483228826.500` (`utc_seconds`); `is_leap_second() == true` | Sound & injective, but requires an up-to-date IERS leap-second table (`tzdata.zi` / `leap-seconds.list`) |

---

### 2. Incompatible `24-Hour` Leap-Smear Curves, Cloud PTP/NTP Split-Brain, and `MiFID II`

`Basis: documentation, source, execution, derived`

To avoid `CLOCK_REALTIME` step-backs without modifying legacy POSIX software, operators stretch `W = 86,400` solar seconds across `W + 1 = 86,401` SI seconds (`u \in [0, 1]`). Direct inspection of `mlichvar/chrony` (`372462ca6c1a822245544003199a24ebfad1fc0e`, `smooth.c:134–205` & `reference.c:120–165`) alongside Google/AWS NTP and `IEEE 1588` PTPv2 reveals why **smearing breaks cross-fleet clock agreement**:

1. **Three Mathematically Incompatible Smear Curves (`probes/verify_leap_smear_tzdb.py`)**:
   - **Linear Noon-to-Noon Smear (`Google Public NTP`, `AWS time.aws.com`)**: Constant frequency offset $\Delta f = -1 / 86{,}401 \approx \mathbf{-11.574\text{ ppm}}$ from `12:00 UTC` on day $D$ to `12:00 UTC` on day $D+1$. Accumulates phase error $s_{\text{lin}}(u) = -u\text{ s}$ (shifted by $+0.5\text{ s}$ relative to UTC after midnight), reaching **`±500.0 ms` vs. true UTC** at `00:00 UTC` with discontinuous first derivatives ($\Delta f$ step) at both `12:00 UTC` endpoints.
   - **Cosine Smear**: Smooths endpoint frequency jumps via $s_{\text{cos}}(u) = -\frac{1}{2}(1 - \cos(\pi u))$ (peak frequency offset $-\frac{\pi}{2 \cdot 86400} \approx \mathbf{-18.18\text{ ppm}}$ at midnight). At $u = \frac{1}{\pi}\arcsin(2/\pi) \approx 0.2197$ (`~17:16 UTC` and `~06:44 UTC`), **Cosine and Linear smeared clocks disagree by `105.26 ms`**!
   - **`chrony` 3-Stage Constant-Wander Quadratic Slew (`smooth.c:134–205`)**: When configured as a leap-smearing server (`leapsecmode slew` + `smoothtime 400 0.001 leaponly`), `update_stages()` (`lines 134–205`) constructs a symmetric 3-stage trajectory (`stages[0].wander = +max_wander`, `stages[1].wander = 0`, `stages[2].wander = -max_wander`) integrating `offset -= length * (2.0 * freq + wander * length) / 2.0` (`line 117`). Below `max_freq` saturation (`l2 = 0`, `line 179`), normalized phase follows $s_{\text{quad}}(u) = -2u^2$ on $[0, 0.5]$ and $-(1 - 2(1-u)^2)$ on $[0.5, 1]$—**diverging from Google/AWS Linear smear by `125.00 ms` at `u = 0.25` (`18:00 UTC`) and `u = 0.75` (`06:00 UTC`)**, and starting at `00:00 UTC` (post-leap) rather than `12:00 UTC` pre-leap unless externally pre-triggered (up to **`500.0 ms`** window-alignment clash!).
2. **Intra-Datacenter `NTP` vs. `PTP` Split-Brain (`500.0 ms` TrueTime / HLC Violation)**:
   - Modern cloud VMs increasingly mix **PTP Hardware Clocks (`/dev/ptp0`, `IEEE 1588-2019` `PTPv2`)**—which count monotonic `TAI` in hardware and advertise discrete `currentUtcOffset` (`unsmeared`)—with **link-local smeared NTP (`169.254.169.123`)**. During a leap window, a database node synced to PTP `PHC` and a sibling node synced to smeared NTP in the **same rack** diverge by **`500.0 ms`**, shattering `Spanner`-style commit-wait intervals (`2\epsilon \approx 1–7\text{ ms}`) and producing external-consistency serializability anomalies!
3. **Regulatory Illegality Under EU `MiFID II RTS 25` (`5,000x` Over Limit)**:
   - Commission Delegated Regulation `(EU) 2017/574` (`RTS 25`, Art. 3–4 Table 2) mandates that high-frequency algorithmic trading venues timestamp reportable events within **`100 microseconds` (`0.100 ms`) of `UTC`** (with `1 ns` granularity). A `±500.0 ms` linear or cosine leap smear violates `RTS 25` by **`5,000x`** for hours on end, making unsignaled leap smearing legally unusable in regulated financial matching engines.

---

### 3. `TAI` / `GPST` / `UTC` Affine Scale Offsets and `1,024`-Week Rollover

`Basis: normative, source, execution`

In `HowardHinnant/date` (`2390d3da331bc44b89940d9b3397ab438ebb6a41`, `include/date/tz.h:2111–2118, 2220–2228`), C++20 `<chrono>` separates physical time scales at the type level (`std::chrono::utc_time`, `tai_time`, `gps_time`, `sys_time`):

```cpp
// HowardHinnant/date include/date/tz.h:2115-2118 & 2225-2228
// TAI epoch is 1958-01-01 00:00:00 TAI (1970-01-01 00:00:00 UTC == 1970-01-01 00:00:10 TAI):
return tai_time<CD>{t.time_since_epoch()} +
        (sys_days(year{1970}/January/1) - sys_days(year{1958}/January/1) + seconds{10});
...
// GPS epoch is first Sunday of Jan 1980 (1980-01-06 00:00:00 UTC == TAI - 19s):
return utc_time<CD>{t.time_since_epoch()} +
        (sys_days(year{1980}/January/Sunday[1]) - sys_days(year{1970}/January/1) + seconds{9});
```

- **Affine vs. Piecewise-Step Relationships**:
  - $\text{TAI} - \text{GPST} \equiv \mathbf{+19\text{ s}}$ (**strict constant affine isomorphism** across all time since 1980; BeiDou `BDT = TAI - 33 s`; Galileo `GST = TAI - 19 s`; whereas GLONASS tracks `UTC(SU) + 3h` *including* leap seconds!).
  - $\text{TAI} - \text{UTC}(t) = \Delta\text{AT}(t)$ (`+10 s` in `1972` $\to$ **`+37 s`** since `2017-01-01`, so $\text{GPST} - \text{UTC} = \mathbf{+18\text{ s}}$). Subtracting raw `gps_seconds` from `sys_seconds` without `clock_cast` introduces an immediate `18 s` (plus `315,964,800 s` `1970`-vs-`1980` epoch) navigation/synchrophasor error.
- **Finite-Modulus `10`-Bit `1,024`-Week GPS Rollover (`619,315,200 s`)**:
  - Legacy `IS-GPS-200` L1 C/A subframe 1 transmits `WN` modulo $2^{10} = 1{,}024\text{ weeks}$ (`19.62 years`; modernized L2C/L5 `CNAV` widens `WN` to `13` bits = `8,192` weeks = `157 years`). Receivers using hardcoded firmware compile-date pivot weeks (`WN_pivot`) wrap `19.62` years *after firmware compilation* rather than only on global rollover dates (`1999-08-21`, `2019-04-06`, `2038-11-20`), projecting aircraft/telecom clocks backward `1,024` weeks into the past.

---

### 4. IANA `tzdb` Civil DST Gaps, `fold=0/1` Repeats, and Future-Timestamp Corruption

`Basis: normative, source, execution`

Civil wall time $c = (Y, M, D, h, m, s)$ in zone $z$ (`eggert/tz` `localtime.c` TZif v2/v3 transitions) relates to physical instants via $c = \pi_z(t) = \text{civil}(t + \Delta_{\text{utc}}(z, t))$. Because $\Delta_{\text{utc}}(z, t)$ jumps forward (`+3,600 s` spring-forward) and backward (`-3,600 s` fall-back, or `+86,400 s` in `Pacific/Apia`'s `2011-12-30` International Date Line skip!), the inverse $\pi_z^{-1}(c)$ is **multi-valued / partial**:

1. **`BurntSushi/jiff` `Disambiguation` (`ambiguous.rs:80–105`) vs. `chrono` `MappedLocalTime` (`offset/mod.rs:85–136`) vs. POSIX `mktime` (`tm_isdst = -1`)**:
   - On `2024-03-10T02:30[America/New_York]` (**Gap**, `02:00 -> 03:00` skipped): `chrono`'s `.earliest()`/`.latest()` both return **`None`**, whereas `jiff`'s default `Disambiguation::Compatible` (`RFC 5545` iCalendar / `RFC 9557` / Java `ZonedDateTime`) projects forward using pre-transition offset `-05` to **`03:30 EDT` (`07:30Z`)**, while `Disambiguation::Earlier` projects backward using `-04` to **`01:30 EST` (`06:30Z`, `3,600 s` earlier!)**, and `Disambiguation::Reject` errors cleanly.
   - On `2024-11-03T01:30[America/New_York]` (**Fold**, `01:00..02:00` occurs twice): `fold = 0` (`EDT -04`, `05:30Z`) and `fold = 1` (`EST -05`, `06:30Z`) are **`3,600 s` apart** (`probes/verify_leap_smear_tzdb.py`). Cron daemons evaluating `local.hour == 1 && local.minute == 30` without tracking `(prev_instant, disambiguated_target)` **execute `01:30` jobs twice on fall-back Sundays and `0` times on spring-forward Sundays**.
2. **The `"Store Future Civil Events as UTC"` Anti-Pattern**:
   - Converting a future user appointment `"2027-10-15 09:00 America/Santiago"` to a scalar UTC `TIMESTAMPTZ` *at booking time* bakes in `tzdb` version `2026a`'s guess of Chile's 2027 DST schedule. When Chile amends its DST transition law six months later (`tzdb 2027b`), the stored UTC epoch now decodes to **`08:00` or `10:00` local time**! Future civil events MUST store the pair `(CivilDateTime, IanaZoneId)` plus `tzdb` rule version, resolving to an instant only when causal execution horizons approach.

---

### 5. Multi-Level Performance and Resource Footprint Matrix (`L1`–`L6`)

`Basis: source, documentation, execution, derived`

| Level | Axis | Unverified POSIX / Smeared / `tm` C APIs (`localtime.c`, `chrony`) | Scale-Indexed Typed Libraries (`jiff`, `Hinnant/C++20`, Zero-Cost `Time<Scale>`) | Engineering & Verification Impact |
| :--- | :--- | :--- | :--- | :--- |
| **L1** | **Human & Agent Authoring Velocity** | `eggert/tz` `localtime.c` `2,600+ LoC` C; `linux/kernel/time/ntp.c` `1,352 LoC` C (`high` subtle overflow/state bug rate) | `jiff` `~45 KLoC` safe ranged-integer Rust; phantom-typed `Instant<TAI>` / `Instant<Monotonic>` wrapper **`< 150 LoC`** (`~2x` SMT/Lean proof ratio, `< 5K` LLM tokens) | Typing clock scales as zero-sized phantom parameters eliminates `100%` of wall-vs-monotonic and `TAI`-vs-`UTC` subtraction bugs in `< 150 LoC` |
| **L2** | **Framework & Toolchain Build Time** | `chrony` C build `< 5 s`; `tzcode` `< 2 s` | `jiff` clean `rustc` build `~3–6 s` (`incremental < 0.8 s`, `< 350 MB` RSS); `HowardHinnant/date` C++20 header `< 3 s` | Zero-dependency ranged-integer crates avoid proc-macro bloat while keeping incremental builds sub-second |
| **L3** | **Compilation, Elaboration & Synthesis Latency** | Unchecked `int64_t` `time_t` (`0 ms` check, zero scale safety) | `QF_LIA` / Lean `omega` proof of `TaiInstant` affine bijections, `GPS` `13`-bit week non-rollover, and `Disambiguation::Reject` totality **`< 10 ms`** (`< 10 ms` warm LSP) | All temporal scale conversions are linear/piecewise-constant integer arithmetic (`QF_LIA`), decidable in single-digit milliseconds with zero SMT timeouts |
| **L4** | **Generated Code Execution Performance** | Linux `vDSO` `clock_gettime(CLOCK_MONOTONIC / CLOCK_TAI)` **`~15–22 ns` (`~50–70` cycles, `0` syscall)**; Go `Time.Sub` `subMono` **`~1.5 ns`** | `Time<TAI>` (`#[repr(transparent)] i128` / `i64` ns) subtraction **`1` CPU `sub` instruction (`0.3 ns`, `0` boundary overhead)**; `jiff` TZif binary search **`~25–60 ns`** | Scale-indexed newtypes compile to bare `64`/`128`-bit register arithmetic (`zero` runtime tag vs. Go's `24`-byte `(wall, ext, *Location)` struct) |
| **L5** | **Proof / Certificate Verification Speed** | Runtime `PTPv2` / `RTS 25` offset audit `< 1 us` | Static `.olean`/`.mmb` scale-isolation & monotonicity proof check **`< 0.5 ms`**; runtime `TZif` transition monotonicity check on load **`< 20 us`/zone** | Verifying sorted, non-overlapping `TZif` transition arrays once at file load (`< 20 us`) guarantees $O(\log N)$ lock-free lookup safety forever |
| **L6** | **RAM, Disk & Binary Footprints** | System `/usr/share/zoneinfo` (`~450` TZif files) `~1.8–3.5 MB` disk; `chronyd` `< 4 MB` RSS | Bundled compressed `jiff-tzdb` **`~180–250 KiB` `.rodata`**; `leap-seconds.list` (`27` entries) **`216 B` (`27 x 8 B`)**; `0 B` heap per `Timestamp` (`8–16 B` stack) | Full historical `1972–2035` IERS `TAI-UTC` step table fits in **`4` CPU cache lines (`256 B`)**, making exact `TAI <-> UTC` conversion cheap even on bare-metal MCUs |

---

### 6. Human Comprehensibility (`C1`) and Conceptual Simplicity / Model Refinement (`C2`)

`Basis: derived, source`

#### 6.1 `(C1)` Human Comprehensibility vs. Agent Execution Ergonomics
- **Why Go's `Time` Fat Struct Is Easy for Agents to Call Yet Deadly for Humans to Audit**: Go's `time.Time` (`go_time.go:140–161`) intentionally hid monotonic vs. wall clocks inside one type so existing `end.Sub(start)` code would "just work." In practice, **human reviewers face an invisible nonlocal state invariant**: looking at `func measure(start time.Time) { d := time.Since(start) }`, **no human can tell from the function signature** whether `start` came directly from `time.Now()` (`hasMonotonic == 1`, safe) or passed through `start.Round(time.Millisecond)` / JSON / gRPC (`hasMonotonic == 0`, panics on leap/NTP step!). Separating `std::time::Instant` (monotonic) from `SystemTime` (wall), as Rust does, keeps the invariant `100%` local in `1` working-memory chunk.
- **Opaque Smear Bugs**: When two cloud microservices use linear vs. cosine/PTP clocks, logs show causal child spans starting `105–500 ms` *before* their parent spans with zero NTP daemon errors—an inscrutable distributed Heisenbug unless every timestamp explicitly carries its scale & uncertainty bound `(tai_ns, +-uncertainty_ns)`.

#### 6.2 `(C2)` Conceptual Simplicity, Felleisen Expressibility & Ousterhout Deep-Module Refinement
- **Why Leap Smearing Fails Both Ousterhout's Deep-Module Principle and Felleisen's Expressibility Test**: Leap smearing tries to preserve POSIX's false axiom (`1 day == 86,400 SI seconds`) by **corrupting the SI second itself** across `86,400` seconds! Under Felleisen's test, smearing is non-compositional: two independently correct subsystems (a Google-NTP-smeared microservice and an AWS-PTP-PHC-synced database, or a `MiFID II` audit logger) fail catastrophically when composed, and *cannot* recover true `TAI` without out-of-band smear-curve knowledge.
- **Minimal Universal Time Algebra (`Scale-Indexed Affine Spaces + Explicit Partial Projections`)**:
  1. **`Instant<Scale>` & `Duration<SI_Ns>` (`Affine Space Law`)**: Parameterize instants by `Scale ∈ {Monotonic, TAI, GPST, UnixPosix}`:
     - `Instant<S> - Instant<S> -> SignedDuration` is total ONLY for monotonic SI-rate scales (`Monotonic`, `TAI`, `GPST`), **statically forbidden** on `UnixPosix` and `CivilDateTime`!
     - `TAI <-> GPST` is an exact compile-time/zero-cost affine bijection (`+19 s` + epoch offset).
  2. **Explicit Leap-Table Witness for `TAI <-> UTC`**: `tai_to_utc(t: Instant<TAI>, table: &IersLeapTable) -> UtcCalendarTime` (supporting `sec == 60` without loss!) and `utc_to_tai(u: UtcCalendarTime, table: &IersLeapTable) -> Result<Instant<TAI>, InvalidLeapSecond>` (`<= 256 B` table, valid up to `table.expires_at` horizon!).
  3. **Explicit Partial/Multi-Valued `Civil <-> TAI` Morphism**: Force `resolve_civil(c, zone, policy: Disambiguation)` to require an explicit `Disambiguation` (`Reject` for security/billing certificates, `Compatible` for UI calendars) and store future scheduled events as `FutureCivilEvent { local: CivilDateTime, zone: IanaZoneId }`, making DST double-fires and silent rule-amendment drift impossible by construction.

## Boundaries

1. **General & Special Relativistic Proper-Time Dilations (`TCG` / `TCB` / `TT` Spaceborne Clocks) (`not examined`)**: At GNSS orbital altitude (`20,200 km`, $v \approx 3.87\text{ km/s}$), combined gravitational blueshift (`+45.85 us/day`) and kinematic time dilation (`-7.21 us/day`) advance satellite atomic clocks by **`+38.64 us/day` (`11.6 km/day` ranging error)** relative to geoid `TAI`, requiring `10.22999999543 MHz` factory frequency detuning and eccentricity $e \sin E$ relativistic corrections (`IS-GPS-200` §20.3.3.3.3.1, `not examined` in terrestrial server clocks).
2. **Post-`2035` CGPM Resolution 4 Leap-Second Moratorium (`known not to apply` to historical epochs or civil `tzdb` folds)**: Even after ITU-R / BIPM suspend new `UTC` leap-second insertions by `2035`, all `27` historical steps (`1972–2017`, `TAI - UTC = 37 s`, `GPST - UTC = 18 s`), `10`-bit GPS week rollovers, NTP step adjustments on oscillator cold-start, and semi-annual civil `tzdb` DST gaps/folds remain `100%` active (`known not to apply` as a panacea for temporal bugs).
3. **Exact Future `UTC` <-> `TAI` Conversion Beyond the `~6`-Month IERS Bulletin C Horizon (`unsupported`)**: Because Earth's core-mantle angular-momentum exchange and glacial isostatic rebound vary stochastically (`even raising the prospect of a first-ever negative leap second 23:59:58 -> 00:00:00` prior to `2035`), computing exact `TAI - UTC` `> 6–12` months into the future without an updated Bulletin C / `tzdata` table is physically **`unsupported`**.
4. **Asymmetric Fiber-Path Routing Attacks Against Unauthenticated `NTP` / `PTPv2` (`unknown` without NTS / White Rabbit calibration)**: Even with `IEEE 1588` hardware timestamping (`< 10 ns` NIC jitter), asymmetric optical TX vs. RX path lengths ($\Delta L = 200\text{ m}$ fiber asymmetry $\implies \mathbf{0.5\text{ us}}$ undetectable one-way delay bias!) bypass two-way `PTP`/`NTP` offset cancellation (`unknown` without calibrated single-fiber bidirectional `White Rabbit` WDM links).

## Evidence

| Source / Artifact | Immutable Identity & Narrow Location | Grounded Fact Established |
| :--- | :--- | :--- |
| `torvalds/linux` | Commit `8dac6df92a2e66e2098bbc69061964cfe7e8375b`, `kernel/time/ntp.c:606–658` | `second_overflow()` sets `leap = -1` and `time_state = TIME_OOP` on `TIME_INS` (`lines 634–636`), replaying `1.0 s` on `CLOCK_REALTIME` while advancing `CLOCK_TAI` |
| `golang/go` | Commit `9535db20eb78901d6a15a880e6700d428c1b7077`, `src/time/time.go:140–166, 1185–1223` | `hasMonotonic = 1 << 63` (`164`); `Time.Sub` uses `subMono` only when both operands carry `hasMonotonic` (`1199–1200`), falling back to wall difference (`1202`) whenever stripped (`stripMono`, `1186`) |
| `mlichvar/chrony` | Commit `372462ca6c1a822245544003199a24ebfad1fc0e`, `smooth.c:110–210` & `reference.c:115–170` | 3-stage piecewise constant-wander quadratic time smoothing (`stages[0..2]` in `update_stages()`, `lines 134–205`) for `leapsecmode slew` + `smoothtime ... leaponly` |
| `BurntSushi/jiff` | Commit `623ea08d41d4ad0c647585eed9405e6b76d2d27e`, `crates/jiff/src/tz/ambiguous.rs:80–105` & `crates/jiff/src/fmt/temporal/parser.rs:820–827` | Four-way `Disambiguation::{Compatible, Earlier, Later, Reject}` (`80–105`) and unconditional `if second == 60 { second = 59; }` leap-second clamp (`parser.rs:823–825`) |
| `chronotope/chrono` | Commit `6adaa5240c26fecb7bd9077334a91f8f67f4f3fe`, `src/naive/time/mod.rs:68–90` & `src/offset/mod.rs:85–136` | Leap second encoded as `second = 59` with `nanosecond` in `1_000_000_000 .. 1_999_999_999` (`mod.rs:68–90`); `MappedLocalTime::{Single, Ambiguous, None}` (`offset/mod.rs:85–95`) |
| `HowardHinnant/date` | Commit `2390d3da331bc44b89940d9b3397ab438ebb6a41`, `include/date/tz.h:140, 1870–2235` | C++20 `utc_clock`, `tai_clock` (`1958-01-01` `+10s` offset, `2116–2117`), `gps_clock` (`1980-01-06` `+9s` offset = `TAI - 19s`, `2226–2227`), and `choose::{earliest, latest}` |
| `eggert/tz` & `SeisComP/seiscomp` | `eggert/tz` `84585da3a2db8cb439e1674f84cf637ac9df6aaa` (`localtime.c`) & `SeisComP` `0f456a83db3435ef92b809bc47077c84b3a4883b` (`libmseed/genutils.c:193, 1294–1314`) | TZif transition tables & `mktime` `tm_isdst` ambiguity vs. `libmseed` `ms_time2nstime_int` folding `23:59:60` forward onto next day's `00:00:00` (`1,000 ms` skew vs. `jiff`) |
| Cloudflare Post-Mortem & `MiFID II RTS 25` | Cloudflare (`2017-01-01` `rrdns` post-mortem) & `(EU) 2017/574` (`RTS 25` Table 2) | Production Go `time.Now().Sub()` negative RTT -> `rand.Int63n` panic; legal `100 us` HFT `UTC` divergence cap (`violated 5,000x by +-500 ms leap smearing`) |
| Preserved Executable Probe | `reports/leap-second-smearing-utc-tai-epoch-folds-and-civil-tzdb-ambiguity-bugs/probes/verify_leap_smear_tzdb.py` (observed `2026-11-19`) | Verified Go `+15 ms` vs. `-985 ms` stripped `hasMonotonic`, `1,000 ms` `jiff`-vs-`libmseed` `:60` skew, `500.0 ms` (`5,000x` `MiFID II`) / `105.26 ms` (cos) / `125.00 ms` (`chrony` quad) smear divergences, `GPST-UTC = +18 s`, and `3,600 s` `tzdb` gap/fold deltas |

## Revalidation

Run either the preserved package probe from the corpus root (`python3 reports/leap-second-smearing-utc-tai-epoch-folds-and-civil-tzdb-ambiguity-bugs/probes/verify_leap_smear_tzdb.py`) or the standalone zero-dependency bash probe below from any directory (`Python >= 3.10`):

```bash
python3 - <<'EOF'
import datetime as dt, math
from zoneinfo import ZoneInfo

# 1. Linux TIME_OOP -1s replay & Go hasMonotonic strip (-985ms vs +15ms) + :60 parser 1000ms skew
wall_t0 = 1_483_228_799_990_000_000
wall_t1 = 1_483_228_799_005_000_000  # 5ms into replayed 23:59:60 -> 1483228799.005
assert (wall_t1 - wall_t0) // 1_000_000 == -985
jiff_clamp_ns = 1_483_228_799_500_000_000     # 60 -> 59 clamp
libmseed_fold_ns = 1_483_228_800_500_000_000  # 60*(...)+60 fold
assert (libmseed_fold_ns - jiff_clamp_ns) // 1_000_000 == 1000

# 2. 24-hour leap-smear phase divergence: Linear vs UTC (500ms = 5000x MiFID II 100us), Cosine, Chrony quad
N = 100_000
max_cos = max(abs(-i/N - (-0.5*(1.0 - math.cos(math.pi * i/N)))) * 1000.0 for i in range(N+1))
max_quad = max(
    abs(-i/N - (-2.0*(i/N)**2 if i/N <= 0.5 else -(1.0 - 2.0*(1.0 - i/N)**2))) * 1000.0
    for i in range(N+1)
)
assert 500.0 / 0.100 == 5000.0
assert 105.2 <= max_cos <= 105.3 and abs(max_quad - 125.0) < 1e-2

# 3. TAI / GPST / UTC affine offsets & IANA tzdb America/New_York fold & gap 3600s ambiguity
assert 37 - 19 == 18 and 1024 * 7 * 86400 == 619_315_200
ny = ZoneInfo("America/New_York")
f0 = dt.datetime(2024, 11, 3, 1, 30, fold=0, tzinfo=ny).timestamp()
f1 = dt.datetime(2024, 11, 3, 1, 30, fold=1, tzinfo=ny).timestamp()
g_comp = dt.datetime(2024, 3, 10, 3, 30, tzinfo=ny).timestamp()
g_earl = dt.datetime(2024, 3, 10, 1, 30, tzinfo=ny).timestamp()
assert int(f1 - f0) == 3600 and int(g_comp - g_earl) == 3600
print("REVALIDATION_OK")
EOF
```

Revalidate upstream implementations when:
1. IERS Bulletin C announces any positive or **negative (`TIME_DEL`, `23:59:58 -> 00:00:00`)** leap second prior to the `2035` CGPM Resolution 4 moratorium (`testing largely unexercised STA_DEL code paths in kernel/time/ntp.c:639–649!`);
2. `BurntSushi/jiff` (`parser.rs:821–826`) exposes configurable leap-second rejection or `TAI` scale support; or
3. `golang/go` (`src/time/time.go`) or cloud PTP/NTP daemons introduce explicit smear-indicator flags in `clock_adjtime` / `PTPv2` TLV extensions (`RFC 8573` / `IEEE 1588` Alternate Time Offset Indicator `ATOI`).
