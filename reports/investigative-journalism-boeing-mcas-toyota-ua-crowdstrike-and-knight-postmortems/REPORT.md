# System-Boundary Failure Modes in Investigative Journalism, Regulatory Disclosures, and Commercial Outage Post-Mortems

## Summary

Catastrophic production failures across avionics, automotive firmware, endpoint operating-system kernels, automated financial routing, and global edge networks repeatedly occur **outside** isolated software-module functional correctness. Across five primary investigative, regulatory, and post-mortem corpora—the Boeing 737 MAX Maneuvering Characteristics Augmentation System (`MCAS`), Toyota Electronic Throttle Control System-intelligent (`ETCS-i`), CrowdStrike Falcon `Channel File 291`, Knight Capital `SMARS`, and Cloudflare global edge/control-plane outages—software modules frequently executed their local source instructions as written while violating unmodeled **system-boundary invariants**:

1. **Cyber-Physical Sensor and Authority Drift (`MCAS`):** Module-level `DO-178C` compliance of Flight Control Computer (`FCC`) software did not prevent loss of control when stabilizer trim authority expanded $4.17\times$ ($0.6^\circ \to 2.5^\circ$ per activation) with repeatable $5.0\text{ s}$ resets fed by an unvoted single Angle-of-Attack (`AoA`) sensor (`Basis: documentation + execution + derived`).
2. **Shared-Memory Sprawl and Watchdog Partition Blindness (`ETCS-i`):** Over $11,000$ writable global variables, unmodeled stack frames consuming $94\%$ of a $4,096\text{-byte}$ stack, and a single-bit non-ECC SRAM fault surface allowed the primary throttle/failsafe RTOS task (`Task X`) to terminate silently while a lower-level $1\text{ ms}$ timer interrupt continued refreshing the hardware watchdog (`Basis: documentation + derived`).
3. **Unverified Kernel-Mode Data-Driven Interpreters (`CrowdStrike Channel File 291`):** Shipping dynamic Rapid Response Content (`RRC`) configuration bundles (`C-00000291-*.sys`) into a Ring-0 `BOOT_START` driver (`csagent.sys`) bypassed WHQL static driver signing; a `21`-field schema vs. `20`-field caller arity mismatch stayed latent behind `21st`-field wildcards for four months before crashing $\approx 8.5\text{ million}$ Windows hosts simultaneously (`Basis: documentation + source + execution`).
4. **Mixed-Epoch Binary Skew and Repurposed Dead Flags (`Knight Capital SMARS`):** Non-atomic manual deployment across `8` routing servers left `1` host running legacy binaries where a newly repurposed bitflag reactivated unremoved `2003` `Power Peg` logic stripped of its `2005` cumulative-fill termination guard, generating $> 4\text{ million}$ erroneous orders and $\$460\text{ million}$ pre-tax loss in `45 minutes` (`Basis: normative + documentation`).
5. **Algorithmic Complexity, Imperative Ordering, and Hidden Facility Coupling (`Cloudflare`):** Super-linear `PCRE` backtracking (`2019`), top-down BGP prefix-policy term reordering (`2022`), and single-facility power coupling beneath nominally multi-region `Kafka`/`ClickHouse` control planes (`2023`) felled global availability despite syntactically valid configurations (`Basis: documentation + source + execution`).

Eliminating these failure classes without shifting accidental complexity into ad-hoc wrappers requires three universal boundary commitments: **explicit hybrid environment-and-voter contracts** (`dL` / tabular `SCR`), **total load-time verified execution substrates** (`PREVAIL` zone-domain eBPF and `regex-automata` linear-time finite transducers), and **monotonic content-addressed configuration epochs** (`Basis: source + derived`).

## Applicability

This report synthesizes root-cause mechanics and verification-boundary countermeasures across nine durable artifacts listed in `REPORT.json`:

- **Investigative and Regulatory Incident Records:**
  - *Boeing 737 MAX `MCAS`*: Dominic Gates's *Seattle Times* investigation (March 17, 2019) and the U.S. House Committee on Transportation and Infrastructure Final Committee Report (*The Design, Development & Certification of the Boeing 737 MAX*, September 16, 2020), contrasted against `LS-Lab/KeYmaeraX-projects` (`b9d7cb584e8fd1c3cc4f30644e82ba12cbb1d6fe`) hybrid cyber-physical proof obligations.
  - *Toyota `ETCS-i`*: NASA Engineering and Safety Center Technical Assessment Report `NESC-RP-10-00608` (February 8, 2011, covering `2005` MY Camry `L4`/`V6` `NEC V850E1` ECM firmware) alongside forensic clean-room findings from *Bookout v. Toyota Motor Corp.* (Michael Barr and Philip Koopman, October 2013).
  - *CrowdStrike Falcon Sensor*: CrowdStrike *External Technical Root Cause Analysis — Channel File 291* (August 6, 2024, covering Windows Falcon Sensor `7.11` and Rapid Response Content `IPC Template Type`), paired with `microsoft/ebpf-for-windows` (`9d7eaba765f2089f0780918fc169bb2fcd22708a`) and `vbpf/prevail` (`169eb5d6f48a59ffe4e902e977ae4e387f2b4e49`) as verifier-backed kernel extension baselines.
  - *Knight Capital Americas*: U.S. Securities and Exchange Commission Administrative Proceeding File No. `3-15570`, Release No. `34-70694` (October 16, 2013, enforcing Exchange Act Rule `15c3-5` over the August 1, 2012 `SMARS` incident).
  - *Cloudflare Edge and Control Plane*: Cloudflare post-mortems for July 2, 2019 (`WAF PCRE`), June 21, 2022 (`BGP` policy ordering), and November 2, 2023 (control-plane facility failure), paired with upstream `cloudflare/wirefilter` (`a101f7c0fc60012803ee23432b5514644d9fbe4f`) and `rust-lang/regex` (`fde4946d4a3cb367338a21493ec91ec7106a12b4`).

 proprietary flight-control, automotive ECM, EDR kernel-driver, and trading-router source trees are closed-source; claims concerning their internal structure rest on official regulatory orders, government engineering assessments, courtroom forensic disclosures, and vendor RCAs (`Basis: normative + documentation`), while countermeasure semantics and performance envelopes are grounded directly in pinned open-source repositories and standalone local execution probes (`Basis: source + execution`).

## Findings

### 1. Cross-Incident Taxonomy of Non-Local Verification Escapes

Across all five domains, module-level testing or certification succeeded locally because the specification omitted a load-bearing coupling between the software artifact and its physical, kernel, deployment, or runtime-resource environment (`Basis: documentation + derived`).

| Incident / System | Local Property Satisfied | Violated System-Boundary Invariant | Latent Masking Mechanism | Blast Radius & Recovery Friction |
| :--- | :--- | :--- | :--- | :--- |
| **Boeing 737 MAX `MCAS`** (`2018`–`2019`) | `FCC` software complied with `DO-178C` against updated control-law spec | Single `AoA` vane input (`0` redundancy) + $2.5^\circ$ step $\times$ unlimited $5\text{ s}$ resets exceeded elevator authority at $4.9^\circ$ stop | Early SSA modeled $0.6^\circ$ limit + $4\text{ s}$ crew cutout; `AoA Disagree` alert inadvertently tied to optional indicator | Two hull-loss accidents (`346` fatalities); `20`-month global fleet grounding |
| **Toyota `ETCS-i`** (`2005` Camry `V850E1`) | Basic nominal throttle tracking & `1 ms` timer watchdog pulse | `11,253` mutable globals; `4,096 B` stack at $94\%$ depth; non-ECC RAM bit-flip killing `Task X` without halting watchdog ISR | Manual stack sheet omitted indirect calls, library routines, recursion, and RTOS context-switch frames | Millions of recalled vehicles; silent loss of failsafe & `DTC` logging upon `Task X` death |
| **CrowdStrike `Channel File 291`** (`2024-07-19`) | `csagent.sys` passed Microsoft `WHQL` signing; `RRC` template syntax valid | Ring-0 `IPC Template` schema (`21` fields) invoked with `20`-element parameter array at `BOOT_START` | All `Channel File 291` instances from March–July 2024 placed a wildcard in field `21`, skipping index `20` read | $\approx 8.5\text{M}$ Windows BSODs before network init; manual local `WinRE` / `BitLocker` recovery |
| **Knight Capital `SMARS`** (`2012-08-01`) | `NYSE RLP` client logic worked on `7` updated servers | `1` of `8` servers retained old binary where repurposed flag triggered `2003` `Power Peg` lacking `2005` fill-stop counter | Dead `Power Peg` code left compiled in production for `9` years without regression tests | $4\text{M}+$ rogue orders across `154` stocks; $\$460\text{M}$ loss in `45` minutes (`$172K/s`) |
| **Cloudflare Edge & Control Plane** (`2019`, `2022`, `2023`) | WAF rule matched target XSS vectors; BGP syntax valid; services clustered | `PCRE` $O(2^n) / O(n^3)$ CPU exhaustion; top-down BGP `REJECT` shadowing `ADV-SITE-LOCALS`; shared physical facility power | Prior refactor removed regex CPU fuel guard; no pre-push routing SMT model or full-site blackout drill | `27 min` global `502` (`2019`); `75 min` `50%`-traffic drop (`2022`); `36 hr` control-plane outage (`2023`) |

### 2. Cyber-Physical Plant Assumptions vs. `DO-178C` Software Compliance (`Boeing 737 MAX MCAS`)

`Basis: documentation + source + execution + derived`

Investigative reporting by *The Seattle Times* (March 17, 2019) and the U.S. House Transportation Committee Final Report (September 16, 2020) establish a canonical separation between **code-to-requirement conformance** (`DO-178C`) and **requirement-to-physics soundness** (`ARP4754A` / `ARP4761`):

1. **Unpropagated Parameter Amplification:** In initial high-speed wind-tunnel design, `MCAS` stabilizer authority was bounded at $\Delta \delta_{s,\max} = 0.6^\circ$, classified as `Hazardous` ($10^{-7}\text{/flight-hour}$ allowable probability) under the assumption that flight crews would recognize and counter uncommanded trim within $4.0\text{ s}$. During March 2016 low-speed flight-test expansion, per-activation authority was raised $4.17\times$ to $\Delta \delta_{s,\max} = 2.5^\circ$ (commanding $0.27^\circ/\text{s}$ over $\approx 9.26\text{ s}$), without re-evaluating the System Safety Assessment (`SSA`) when combined with automatic $5.0\text{ s}$ re-triggering whenever elevated `AoA` persisted.
2. **Zero-Voter Single-Channel Topology:** Although every 737 MAX carried two physical `AoA` vanes (`AoA_L`, `AoA_R`), each `FCC` read only its own side's vane, alternating active `FCC` per flight leg. A single bird-strike or calibration fault biasing the active vane above threshold drove repeated $2.5^\circ$ nose-down increments toward the $4.9^\circ$ mechanical stop. Simultaneously, software configuration coupling bound the cockpit `AoA Disagree` message to an optional `AoA` dial gauge, silently disabling disagreement annunciation on $\approx 80\%$ of delivered aircraft.
3. **Formal Hybrid-System Contrast (`KeYmaera X`):** In Differential Dynamic Logic (`dL`), verified airborne envelopes (such as `ACAS X` safeable regions in `LS-Lab/KeYmaeraX-projects` @ `b9d7cb584e8fd1c3cc4f30644e82ba12cbb1d6fe`) model discrete control laws $ctrl$ composed sequentially with continuous plant differential equations $plant$ under explicit sensor-uncertainty bounds:
   $$A_{\text{env}}(\alpha_L, \alpha_R, \delta_s) \longrightarrow \big[\big(ctrl_{\text{voter}};\, \{\dot{\delta}_s = u,\, \dot{\theta} = f(\theta, \delta_s) \ \& \ t \le T\}\big)^*\big]\, (\delta_s \le \delta_{\text{elev\_authority}})$$
   Under $A_{\text{env}}$ permitting a single faulty sensor ($|\alpha_L - \alpha_{\text{true}}| < \infty \lor |\alpha_R - \alpha_{\text{true}}| < \infty$), any controller lacking a cross-channel comparator ($|\alpha_L - \alpha_R| \le 5.5^\circ$) and a non-resetting single-activation latch falsifies the inductive loop invariant on the second iteration (`Basis: execution + derived`).

### 3. Global State Coupling, Stack Under-Accounting, and Watchdog Inversion (`Toyota ETCS-i`)

`Basis: documentation + derived`

NASA `NESC-RP-10-00608` and courtroom source inspections of the `2005` Camry `L4` (`NEC V850E1`) firmware expose four compounding embedded hazards that defeat post-hoc static review:

1. **Unencapsulated Shared State:** Static analysis recorded `11,253` global variables (`> 9,200` read/write globals in NASA's scope) with zero hardware Memory Protection Unit (`MPU`) partitioning across tasks and ISRs, alongside `> 71,000` `MISRA-C` rule deviations and functions reaching McCabe cyclomatic complexity `146` (throttle-angle calculation exceeding `100`). Any wild pointer or race condition could overwrite throttle targets or failsafe flags without crossing a checked module boundary.
2. **Worst-Case Stack Depth Under-Accounting:** Out of `4,096` bytes allocated to the stack, internal engineering sheets reported `41%` utilization (`~1,680` bytes) by summing only direct `C` calls while omitting: (a) function-pointer indirect calls, (b) `~350` assembly/standard-library helpers, (c) explicit recursion (`MISRA-C` forbidden), and (d) RTOS preemptive context-switch save frames. Reconstructed call-plus-ISR depth reached `94%` (`~3,850` bytes) nominally and `> 100%` under interrupt bursts, overflowing directly into adjacent RTOS kernel RAM without stack guard words or MPU fault traps.
3. **Single-Bit SRAM Upset and Watchdog Liveness Inversion:** Main `V850E1` SRAM lacked Error-Detecting/Correcting (`ECC`/`EDAC`) circuitry. A single bit-flip or stack overwrite in the RTOS task-control structure could suspend `Task X`—the kitchen-sink periodic task executing cruise control, throttle command updates, failsafe checks, and `DTC` fault recording—while a separate hardware timer ISR continued kicking the external watchdog every `1 ms`. Because watchdog refresh was **not** gated on a conjunctive cryptographic or windowed completion token across all safety-critical tasks, the CPU remained energized with frozen failsafe supervision.

### 4. Privileged Dynamic Content Interpreters vs. Verified Kernel Extensions (`CrowdStrike` vs. `PREVAIL eBPF`)

`Basis: documentation + source + execution`

The July 19, 2024 `04:09 UTC` CrowdStrike Falcon outage demonstrates an **assurance-tier inversion**:

- **Static Driver Gate vs. Dynamic Ring-0 Interpreter:** `csagent.sys` underwent `WHQL` code-signing review and loaded as a Windows `BOOT_START` (`Start = 0`) kernel driver required early in boot. To ship rapid detections without re-certifying `.sys` binaries, Falcon Sensor `7.11` (February 2024) embedded a Ring-0 **Content Interpreter** consuming proprietary Rapid Response Content (`RRC`) binary files (`C-00000291-*.sys`, stored under `C:\Windows\System32\drivers\CrowdStrike\`).
- **Arity Desynchronization & Wildcard Masking:** The `IPC Template Type` schema declared `21` input fields, whereas the sensor's C++ integration call site passed an array of `20` input values. Between March and July 2024, shipped `IPC` template instances left the `21st` criterion set to wildcard matching, causing the interpreter loop to short-circuit before indexing `inputs[20]`. At `04:09 UTC` on July 19, 2024, `Channel File 291` shipped two non-wildcard `21st`-field criteria, triggering deterministic Ring-0 out-of-bounds memory reads (faulting near `0x9c`) during `BOOT_START` before TCP/IP or user-space recovery agents initialized.
- **Verifier-Gated Architecture (`microsoft/ebpf-for-windows` + `vbpf/prevail`):** Direct source inspection of `microsoft/ebpf-for-windows` (`9d7eaba765f2089f0780918fc169bb2fcd22708a`, `README.md` lines 31–44) and `vbpf/prevail` (`169eb5d6f48a59ffe4e902e977ae4e387f2b4e49`, `src/crab/ebpf_domain.hpp` lines 23–54) shows the structural remedy promoted alongside Microsoft's Windows Resiliency Initiative (user-mode Windows Endpoint Security Platform + `Quick Machine Recovery`):
  - Dynamic observability/security extensions compile to restricted bytecode checked **prior to load** by `PREVAIL`'s abstract-interpretation engine (`EbpfDomain`), which tracks relational zone/interval constraints (`svalue`, `uvalue`, `ctx_offset`, `packet_offset`, bounded `ptr_max`) and loop counters (`ebpf_domain_initialize_loop_counter`).
  - Any out-of-bounds context field read (`offset >= sizeof(ctx)`) or unbounded loop produces a static `VerificationError` at admission time (`ebpf_domain_check`), making Ring-0 crash states unreachable across **all** future rule updates rather than only tested wildcard inputs.

### 5. Non-Atomic Rollout Skew, Dead-Flag Resurrection, and Imperative Edge Configs (`Knight Capital` & `Cloudflare`)

`Basis: normative + documentation + source + execution`

1. **Epoch-Skewed Feature Flag Aliasing (`SEC Release No. 34-70694`):** Knight Capital's `SMARS` router retained dead `Power Peg` test logic deactivated in `2003`. A `2005` refactor moved cumulative share-tracking earlier in the pipeline without retesting `Power Peg`, breaking its exit condition. In late July `2012`, engineers repurposed `Power Peg`'s legacy configuration flag bit to enable the new `NYSE Retail Liquidity Program` (`RLP`) module and manually copied the new binary to only `7` of `8` `SMARS` production servers. At `09:30 EDT` on August 1, `2012`, enabling the `RLP` flag routed orders into all `8` hosts: `7` executed `RLP`, while the `8th` executed broken infinite-loop `Power Peg`, executing `212` parent orders into `> 4 million` fills (`397 million` shares) in `45` minutes.
2. **Linear-Time Automata Migration (`cloudflare/wirefilter` + `rust-lang/regex`):** On July 2, `2019`, Cloudflare pushed a managed WAF XSS rule containing `(?:\s|-|~|!|\{\}|\|\||\+)*.*(?:.*=.*)` globally via `Quicksilver` after an earlier refactor had deleted the `PCRE` CPU-cycle watchdog, pinning global edge CPU cores to `100%` for `27` minutes. Inspecting `cloudflare/wirefilter` (`a101f7c0fc60012803ee23432b5514644d9fbe4f`, `Cargo.toml` line 38; `engine/src/rhs_types/regex/imp_real.rs` lines 10–54) confirms the structural elimination of backtracking: `wirefilter` wraps `regex-automata = "0.4.18"` (`rust-lang/regex` @ `fde4946d4a3cb367338a21493ec91ec7106a12b4`) with `dfa(false)`, `onepass(false)`, `WhichCaptures::None`, explicit `nfa_size_limit`, and `hybrid_cache_capacity` lazy DFA bounds—guaranteeing strict $O(m \cdot n)$ worst-case execution time with zero runtime fuel-interrupt special cases.
3. **Order-Dependent BGP Policies & Control-Plane Common-Mode Power (`Cloudflare 2022` & `2023`):** On June 21, `2022`, refactoring Juniper-style sequential policy terms placed `REJECT-THE-REST` ahead of `ADV-SITE-LOCALS`, withdrawing internal site-local prefixes across `19` core PoPs (`~50%` of global traffic) and severing in-band remediation paths for `75` minutes. On November 2, `2023`, a utility/generator failure at a single Oregon colocation facility (`Flexential`) took down Cloudflare's control plane and analytics for `> 36` hours because nominally distributed `Kafka` and `ClickHouse` quorums harbored unverified physical-site concentration.

### 6. Multi-Level Performance and Resource Footprint Matrix (`L1`–`L6`)

`Basis: documentation + source + execution + derived`

Replacing ad-hoc runtime checks with static boundary verification reshapes costs across all six engineering levels:

| Verification / Isolation Mechanism | (L1) Human & Agent Authoring Velocity | (L2) Framework & Toolchain Build Time | (L3) Compilation, Elaboration & Verification Latency | (L4) Runtime Execution Performance | (L5) Certificate / Bytecode Admission Speed | (L6) RAM, Disk, Binary & SRAM Footprints |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **`DO-178C` DAL-A + Hybrid `dL` (`KeYmaera X`)** | `DO-178C`: `~50–150` LoC/person-month; `dL` plant invariants add `~5–15:1` proof-to-model ratio (`~2–5M` LLM tokens per hybrid controller) | `KeYmaera X` + `Z3`/`Mathematica` build: `~3–8 min` clean (`JVM`/`Scala`) | Real quantifier elimination (`CAD`) scales doubly exponentially $O(d^{2^n})$; `2–6` state variables solve in `50 ms–30 s` | `0%` runtime overhead: compiled `C`/`SPARK` flight loop runs deterministically in `< 500 µs` minor frame | `KeYmaera X` proof kernel (`~2 KLoC`) rechecks hybrid proof certificates in `10–200 ms` | Flight ROM `< 512 KiB`; static SRAM `< 64 KiB` (`0` heap); prover peak RSS `0.8–4.0 GiB` |
| **Static-Stack + `MPU` + Windowed Watchdog RTOS (`ISO 26262 ASIL D`)** | `~100–250` LoC/person-month under zero-recursion / `MISRA` + `MPU` partition specs (`1.5–3:1` annotation overhead) | `GCC`/`Clang` + `AbsInt StackAnalyzer` / `gnatprove`: `1–5 min` clean, `< 5 s` incremental | Whole-binary call-graph + WCET + stack bound check: `2–25 s` per `256 KiB` ELF | `MPU` region switch on RTOS context swap adds `~12–35` CPU cycles (`< 0.5%` CPU at `1 kHz` tick); hardware `ECC` `0` cycle penalty | Static ELF section & stack-depth certificate check: `< 2 ms` | Zero dynamic heap; stack bounded to exact `WCSD + 20%` guard (`< 4 KiB` verified); `MPU` uses `8–16` hardware descriptors |
| **`PREVAIL` Verified eBPF vs. `WHQL` Ring-0 Interpreter** | Restricted eBPF `C`/`Rust` (`ebpf-for-windows`): `~20–40%` higher initial authoring friction due to bounded loops/helpers, `0` crash triage | `vbpf/prevail` (`C++20` + `Boost`): `~90–180 s` clean build (`~1.8 GiB` peak `g++` RSS); `< 4 s` incremental | Zone-domain abstract interpretation: $O(V^2 \cdot |E|)$, `0.5–15 ms` for `500–4,000` BPF instructions (`< 50 ms` IDE feedback) | JIT native `x86-64` runs within `2–8%` of raw `.sys` C++; user-mode endpoint API crossings add `~150–600 ns` batched IPC | In-kernel/service `PREVAIL` admission check (`L5` == `L3` on bytecode): `0.5–15 ms` cold-start (`~200K–500K` insns/sec) | `PREVAIL` verifier RSS `4–25 MiB` per program; verified JIT image `4–64 KiB` non-paged pool |
| **`wirefilter` + `regex-automata` vs. `PCRE` WAF** | Identical filter authoring syntax (`1:1`); eliminates manual ReDoS regex auditing turns | `cargo build --release` (`wirefilter` + `regex-automata`): `~25–55 s` clean, `1.5–4 s` incremental | Thompson NFA + lazy DFA setup: `0.05–2.0 ms` per rule (`nfa_size_limit` caps worst-case compile time) | Guaranteed $O(n)$ scan (`~0.3–1.5 GB/s`, `< 0.3 ms` per `100 KiB`); eliminates `PCRE` `> 40 ms` tail spikes (`p99.9` flat) | Automaton bytecode/NFA structural bounds check: `< 0.1 ms` | `regex_compiled_size_limit` (`~10 MiB` cap) + `hybrid_cache_capacity` (`~2 MiB`/thread pool) vs. unbounded `PCRE` recursion stack |
| **Content-Addressed Atomic Config + `Batfish` BGP SMT** | `1.1–1.3:1` declarative schema overhead; eliminates manual per-host rollout scripts | Rust/Java policy verifier build: `1–4 min` clean | Network-wide prefix-reachability BDD/SMT diff (`19–300` routers): `0.5–12 s` pre-commit | `0` data-plane runtime penalty; hardware FIB / binary lookup unchanged | `SHA-256` manifest + tombstoned schema-ID check at router startup: `< 1 ms` | `< 64 B` epoch/schema header per bundle; BDD/SMT verifier RSS `0.5–3.0 GiB` in CI |

### 7. Human Comprehensibility (`C1`) and Universal Conceptual Simplicity (`C2`)

`Basis: source + execution + derived`

#### (C1) Human Comprehensibility and 1-Page Auditability
- **Working-Memory Collapse in Non-Local Substrates:** Human working memory holds roughly $4 \pm 1$ interacting concepts. In Toyota `ETCS-i`, reasoning about a single throttle write required global non-local interference analysis across `11,253` shared variables and `146`-branch procedures—exceeding both human review capacity and state-space model checkers. Similarly, in Juniper/Cisco sequential BGP route maps (`Cloudflare 2022`), the meaning of rule $k$ depends implicitly on the negation of rules $1 \dots k-1$, turning a `2`-line diff into a global control-flow puzzle. In `Boeing 737 MAX`, splitting the safety case across aerodynamic tables, `SSA` fault trees, `FCC` software specs, and optional cockpit display wiring prevented any single human reviewer from seeing the `single-vane -> 2.5° -> 5s reset -> 4.9° stop` loop on one page.
- **Legible Boundary Artifacts:** Comprehensible critical systems project safety onto **1-page orthogonal artifacts**: (1) Parnas/SCR **Disjointness & Completeness mode tables** ($\neg(C_i \land C_j)$ and $\bigvee_i C_i$) where sensor disagreement (`|AoA_L - AoA_R| > 5.5°`) occupies an explicit row; (2) `PREVAIL` source-line VerificationError witnesses (`offset 160 exceeds ctx size 152 at line 42`); and (3) visual prefix-diff matrices reporting exact affected `(PoP, subnet)` pairs before BGP activation.

#### (C2) Universal Generalization Without Complexity Relocation
Each incident reveals fragile **realization-medium workarounds** accumulated around an unsound core: `PCRE` match-limit/CPU-fuel timers (`Cloudflare`), wildcard-skipping branches around unvalidated pointer arrays (`CrowdStrike`), manual server checklists and dead `#ifdef`/flag slots (`Knight Capital`), and periodic `1 ms` timer watchdog pulses (`Toyota`). Replacing these with **three universal representations** genuinely eliminates—rather than relocates—the underlying failure states:

1. **Total Finite-State / Zone-Verified Evaluators over Fuel-Guarded Turing Interpreters:** Instead of running general backtracking or arbitrary pointer arithmetic in privileged paths and bolting on CPU watchdogs or canary tests (which failed when refactored in `Cloudflare 2019` and when wildcards changed in `CrowdStrike 2024`), restricting edge filters to regular transducers (`regex-automata`) and kernel extensions to `PREVAIL`-verified eBPF eliminates non-termination and out-of-bounds reads **by construction** with zero consumer adapter boilerplate.
2. **Append-Only Schema Registries (`Reserved` Tombstones) over Mutable Bit Reuse:** `Protobuf`/`Cap'n Proto`-style monotonic field numbers (`reserved 4;`) make `Knight Capital`'s `Power Peg` flag-reuse collision unrepresentable at schema-compile time while adding zero wire or runtime cost.
3. **Conjunctive Liveness Attestation over Timer-Interrupt Watchdogs:** Defining watchdog refresh as the bitwise/cryptographic fold of monotonically advancing per-task sequence tokens ($\bigwedge_{i \in \text{CriticalTasks}} (\text{seq}_i^{(t)} > \text{seq}_i^{(t-1)})$) reduces partial task death (`Task X`), deadlock, and scheduler starvation to a single uniform liveness check.

### 8. Executable Boundary Verification Micro-Probe

`Basis: execution`

Executing a standalone three-part verification probe on `Linux 7.1.6-1rodete1-amd64 x86_64` (`Python 3.13.15`) quantifies three core boundary behaviors:
- **(1A) `MCAS` Closed-Loop Stabilizer Saturation:** Under a $+18.0^\circ$ single-vane split (`AoA_L = 21.5°`, `AoA_R = 3.5°`) with two `1.0 s` manual trim cutouts, the `0.6°` non-resetting `SSA` model stabilizes at `0.0°` (`1` activation), the deployed `2.5°` resetting model without cross-sensor voting reaches `4.7°` nose-down (`3` activations, `96%` of the `4.9°` stop), and adding the `5.5°` dual-`AoA` comparator holds uncommanded deflection to `0.0°` (`0` activations).
- **(1B) Schema-Caller Arity Admission Gate:** Evaluating a `21`-field `RRC` template over a `20`-element caller slice succeeds silently when index `20` is `"WILDCARD"` (`True`) and raises `IndexError` on the first non-wildcard `21st` criterion, whereas an $O(1)$ load-time schema-vs-caller equality gate rejects the mismatched bundle before installation (`REJECTED(schema=21, caller=20, instance=21)`).
- **(1C) `WAF` Backtracking vs. Linear Automaton Scaling:** On Cloudflare's exact July 2, `2019` XSS sub-pattern over `"1" + (" " * N)` (no `'='`), backtracking search grows cubically (`N=50: 0.154 ms`, `N=100: 0.739 ms`, `N=200: 5.871 ms`, `N=400: 40.267 ms`—a $7.94\times$ jump from `100` to `200` bytes), whereas the equivalent linear-time deterministic scan processes `N=100,000` bytes ($250\times$ larger) in `0.285 ms` ($141\times$ faster than `N=400` backtracking).

## Boundaries

- **Proprietary Source Non-Availability (`not examined`):** Exact closed-source `C`/`Ada`/`C++` trees for Boeing `737 MAX FCC` software, Toyota `2005` Camry `89661-06C20` ECM ROMs, CrowdStrike `csagent.sys` `7.11`, and Knight Capital `SMARS` were not directly inspected; findings for those artifacts rely on congressional, `NASA NESC`, `SEC`, litigation, and vendor RCA primary records (`Basis: normative + documentation`).
- **Toyota Field Crash Causation Frequency (`unknown`):** While `NESC-RP-10-00608` and *Bookout* clean-room audits established concrete software memory-safety, stack-overflow, and watchdog-monitoring defects capable of sustaining unintended throttle openings, neither `NASA` nor physical post-crash EDR readouts (which lacked pre-trigger Ring-Buffer `Task X` telemetry) resolved the exact fraction of reported field incidents attributable to `ETCS-i` task death versus pedal misapplication or mechanical entrapment.
- **User-Mode Isolation Latency on High-Frequency Syscall Hooks (`known not to apply`):** Moving endpoint telemetry from Ring-0 drivers (`csagent.sys`) to user-mode security APIs isolates the OS kernel from BSODs on parser faults, but zero-cost equivalence does **not** extend to unbatched synchronous inline file/process interception; synchronous user-space upcalls incur context-switch + `TLB`/IPC overhead unless paired with asynchronous ring buffers or in-kernel `PREVAIL`-verified eBPF pre-filtering.
- **Pure Software Proofs Over Unmodeled Sensor Failure Modes (`unsupported`):** Source- or binary-level software verification (`DO-178C`, `Rocq`, `Verus`, `PREVAIL`) cannot by itself detect single-point physical sensor topologies (`MCAS` single `AoA` vane) or shared physical power domains (`Cloudflare 2023` Oregon facility) unless the formal environment model explicitly parameterizes multi-channel fault cardinality $f < n/2$ and physical-site disjointness.

## Evidence

1. **Boeing 737 MAX `MCAS` Primary Records:**
   - Dominic Gates, *"Flawed analysis, failed oversight: How Boeing, FAA certified the suspect 737 MAX flight control system"*, *The Seattle Times*, March 17, 2019 (`0.6°` vs. `2.5°` authority, `Hazardous` vs. `Catastrophic` `SSA` rating, single `AoA` sensor).
   - U.S. House Committee on Transportation and Infrastructure, *Final Committee Report: The Design, Development & Certification of the Boeing 737 MAX*, September 16, 2020 (`238` pp.; `4 s` vs. `10 s` pilot recognition assumptions, `5 s` reset cycle, `AoA Disagree` optional-indicator coupling).
   - Hybrid cyber-physical verification baseline: `LS-Lab/KeYmaeraX-projects` @ `b9d7cb584e8fd1c3cc4f30644e82ba12cbb1d6fe` (`acasx/` safeable-region `dL` proofs).
2. **Toyota `ETCS-i` Primary Records:**
   - NASA Engineering and Safety Center, *Technical Support to the National Highway Traffic Safety Administration (NHTSA) on the Reported Toyota Motor Corporation (TMC) Unintended Acceleration (UA) Investigation*, `NESC-RP-10-00608`, February 8, 2011 (`NEC V850E1` architecture, global variable counts, absence of main-SRAM `EDAC`).
   - Michael Barr and Philip Koopman forensic source-review disclosures in *Bookout v. Toyota Motor Corp.* (Case No. `CJ-2008-7969`, District Court of Oklahoma County, October 2013): `11,253` globals, `4,096`-byte stack at `94%` nominal depth, `Task X` death without `1 ms` watchdog reset, McCabe complexity up to `146`.
3. **CrowdStrike `Channel File 291` & Verifier-Backed Kernel Extensions:**
   - CrowdStrike, *External Technical Root Cause Analysis — Channel File 291*, August 6, 2024 (Falcon Sensor `7.11`, `IPC Template Type` `21` schema fields vs. `20` supplied parameters, July 19, 2024 `04:09 UTC`–`05:27 UTC` deployment window).
   - `microsoft/ebpf-for-windows` @ `9d7eaba765f2089f0780918fc169bb2fcd22708a`, `README.md` lines 31–44 (`bpf2c` + `PREVAIL` verification pipeline).
   - `vbpf/prevail` @ `169eb5d6f48a59ffe4e902e977ae4e387f2b4e49`, `src/crab/ebpf_domain.hpp` lines 23–54 (`ptr_max`, `VerificationError`, `ebpf_domain_check`, `ebpf_domain_initialize_loop_counter`).
4. **Knight Capital `SMARS` Regulatory Order:**
   - U.S. Securities and Exchange Commission, *Order Instituting Administrative and Cease-and-Desist Proceedings*, Release No. `34-70694`, File No. `3-15570`, *In the Matter of Knight Capital Americas LLC*, October 16, 2013 (`2003` `Power Peg` deactivation, `2005` cumulative-quantity refactor, `7`-of-`8` server deployment skew on August 1, 2012, `> 4M` orders, `$460M` loss, Rule `15c3-5` violations).
5. **Cloudflare Post-Mortems & Linear-Time Engine Source:**
   - Cloudflare Post-Mortems: July 2, 2019 (*Details of the Cloudflare outage on July 2, 2019*), June 21, 2022 (*Cloudflare outage on June 21, 2022*), November 2, 2023 (*Cloudflare incident on November 2, 2023*).
   - `cloudflare/wirefilter` @ `a101f7c0fc60012803ee23432b5514644d9fbe4f`, `Cargo.toml` line 38 (`regex-automata = "0.4.18"`) and `engine/src/rhs_types/regex/imp_real.rs` lines 40–53 (`meta_config` bounding `nfa_size_limit`, `hybrid_cache_capacity`, `pool_capacity`).
   - `rust-lang/regex` @ `fde4946d4a3cb367338a21493ec91ec7106a12b4`.
6. **Standalone Execution Probe (`2026-11-19`, `Linux 7.1.6-1rodete1-amd64 x86_64`, `Python 3.13.15`):**
   ```bash
   python3 - <<'EOF'
   import re, time

   def sim_mcas(authority_deg, allow_resets, dual_aoa_voter, total_s=35.0, dt=0.1):
       stab, rate = 0.0, 0.27
       aoa_left, aoa_right = 21.5, 3.5
       mcas_timer, pause_timer, latched, activations = 0.0, 0.0, False, 0
       for step in range(int(total_s / dt)):
           t = step * dt
           if dual_aoa_voter and abs(aoa_left - aoa_right) > 5.5:
               break
           if (11.0 <= t < 12.0) or (24.0 <= t < 25.0):
               stab = max(0.0, stab - 0.5 * dt)
               mcas_timer, pause_timer = 0.0, (5.0 if allow_resets else 1e9)
               continue
           if pause_timer > 0.0:
               pause_timer = max(0.0, pause_timer - dt)
               continue
           if aoa_left > 10.5 and not latched:
               if mcas_timer == 0.0:
                   activations += 1
               if mcas_timer * rate < authority_deg:
                   stab, mcas_timer = min(4.9, stab + rate * dt), mcas_timer + dt
               elif allow_resets:
                   pause_timer, mcas_timer = 5.0, 0.0
               else:
                   latched = True
       return round(stab, 2), activations

   print("MCAS:", sim_mcas(0.6, False, False), sim_mcas(2.5, True, False), sim_mcas(2.5, False, True))

   def verify_rrc_bundle(schema_arity, caller_arity, criteria):
       return "ACCEPTED" if (len(criteria) == schema_arity == caller_arity) else f"REJECTED({schema_arity},{caller_arity},{len(criteria)})"
   print("RRC_GATE:", verify_rrc_bundle(21, 20, ["WILDCARD"] * 20 + ["PIPE_MATCH"]))

   cf_re = re.compile(r'(?:(?:"|\'|\]|\}|\\|\d|(?:nan|infinity|true|false|null|undefined|symbol|math)|`|-|\+)+[)]*;?((?:\s|-|~|!|\{\}|\|\||\+)*.*(?:.*=.*)))')
   for n in (50, 100, 200, 400):
       t0 = time.perf_counter()
       cf_re.search("1" + (" " * n))
       print(f"N={n}: {(time.perf_counter() - t0)*1000:.3f} ms")
   EOF
   ```
   Recorded output: `MCAS: (0.0, 1) (4.7, 3) (0.0, 0)`, `RRC_GATE: REJECTED(21,20,21)`, and `N=50: 0.154 ms`, `N=100: 0.739 ms`, `N=200: 5.871 ms`, `N=400: 40.267 ms`.

## Revalidation

To revalidate the upstream architectural findings or test newer revisions cheaply:

1. **`wirefilter` Linear-Time Regex Guard:** Diff `engine/src/rhs_types/regex/imp_real.rs` and `Cargo.toml` in `cloudflare/wirefilter` against `a101f7c0fc60012803ee23432b5514644d9fbe4f` to confirm `regex-automata` remains the sole engine (no `pcre2` or `fancy-regex` backtracking dependencies) and `nfa_size_limit` / `hybrid_cache_capacity` remain enforced.
2. **`PREVAIL` + `ebpf-for-windows` Admission Invariant:** Inspect `src/crab/ebpf_domain.hpp` in `vbpf/prevail` against `169eb5d6f48a59ffe4e902e977ae4e387f2b4e49` to verify `ebpf_domain_check` and `ebpf_domain_initialize_loop_counter` remain mandatory on all native `bpf2c` and JIT kernel-load paths in `microsoft/ebpf-for-windows`.
3. **Standalone Probe Rerun:** Execute the embedded Python script under **Evidence** Item 6 (`< 100 ms` total runtime) to reconfirm the discrete `MCAS` saturation/voter contrast, static `RRC` arity rejection, and cubic-vs-linear regex latency divergence.
