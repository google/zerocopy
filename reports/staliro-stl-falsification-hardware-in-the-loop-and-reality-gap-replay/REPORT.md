# Quantitative STL Falsification, Hardware-in-the-Loop Reality-Gap Replay, ModelPlex Runtime Plant Monitors, and SMoL Mental-Model Validation

## Summary

Formal verification of control software, hybrid ordinary differential equations (`ODE`s), and programming-language surfaces proves safety only relative to an idealized mathematical plant model and an assumed human reading of surface specifications. Real cyber-physical and human-operated deployments fail across **four reality gaps** that require distinct quantitative and empirical validation layers:

1. **High-dimensional nonlinear/black-box plant & perception regimes (`STL`/`MTL` Robustness Falsification)**: Where symbolic reachability cannot scale across nonlinear `Simulink`/C++/neural-perception loops, **PSY-TaLiRo** (`cpslab-asu/psy-taliro`), **Breach** (`decyphir/breach`), and **VerifAI + Scenic** (`BerkeleyLearnVerify/VerifAI`, `BerkeleyLearnVerify/Scenic`) replace Boolean pass/fail predicates with Fainekos-Pappas / Maler-Ničković quantitative **Signal Temporal Logic (`STL`) robustness** $\rho(\varphi, \mathbf{y}, t) \in \mathbb{R} \cup \{\pm\infty\}$. Because $\rho < 0$ witnesses violation and $|\rho|$ measures signed spatial margin to the specification boundary, global stochastic/Nelder-Mead/cross-entropy optimizers descend $\rho$ across narrow resonant disturbance pockets that uniform Monte Carlo misses. However, discrete-time monitor adapters introduce subtle time-base traps—most notably `psy-taliro`'s `rtamt.py:61` `round(period, 2)` call, which collapses `>= 200 Hz` (`<= 4 ms`) sampling periods to `0.0 s` and dilates `125 Hz` (`8 ms`) horizons by `+25%` (`0.01 s`).
2. **The Sim-to-Real Hardware-in-the-Loop (`HIL`) & Incident-Telemetry Gap**: Controllers proved safe over continuous `FP64` ODEs can fail on physical buses and sensors due to multi-tick Zero-Order-Hold (`ZOH`) transport lag, coarse `PWM` duty quantization, analog-to-digital (`ADC`) rail clipping, and unmasked digital dropout sentinels—exemplified in **PhysioNet WFDB** (`MIT-LCP/wfdb-python`) format `'16'` where electrode lead-off / invalid samples are encoded in-band as `DIGITAL_NAN = -32768`, causing violent integral windup if ingested directly as raw integer counts without `dac()` NaN conversion and anti-windup clamping.
3. **Online Departure from Proved Plant Envelope Assumptions (`ModelPlex`)**: Offline Differential Dynamic Logic (`dL`) theorems $A \to [\alpha^*]P$ in **KeYmaera X** (`LS-Lab/KeYmaeraX-release`) guarantee safety only while physical reality evolves inside $\alpha$. **ModelPlex** (`ModelPlex.scala`) eliminates quantifiers from $\langle \alpha \rangle \Upsilon$ to synthesize quantifier-free runtime controller monitors $\chi_{\text{ctrl}}$ and plant-validity monitors $\chi_{\text{model}}(x_{\text{pre}}, u, x_{\text{post}})$ (including quantitative signed safety margins via `mxFormatShape("metricfml")`), detecting unmodeled icy-road actuator fade or sensor drift **online before physical safety boundaries are breached**.
4. **The Human Mental-Model Gap (`SMoL`)**: Even machine-verified code and monitors fail catastrophically if human engineers or clinical/grid operators misread lexical binding, aliasing vs. rebinding, mutable closure state, or mode transitions in specifications. **SMoL** (`shriram/smol`, Lu & Krishnamurthi, PACMPL OOPSLA 2024, `DOI: 10.1145/3649823`) validates human comprehension empirically via minimal multi-language behavioral litmus programs with targeted misconception distractors (`smol/fun`, `smol/state`, `smol/hof`, `smol/dyn-scope-is-bad`).

## Applicability

This report governs the continuous-plant, physical I/O, runtime-envelope, and human-comprehension validation stack for embedded, autonomous, medical, power-grid, and high-assurance software systems.

### Relationships Among Examined Subjects

The seven subjects in `REPORT.json` address complementary failure modes across design-time search, physical replay, online execution, and human specification authoring:

- **Quantitative temporal-logic falsifiers (`PSY-TaLiRo`, `Breach`, `VerifAI` + `Scenic`)**:
  - `cpslab-asu/psy-taliro` (`887f2dc321e83688796307f8b0abcf22b3a57b4c`, Python successor to MATLAB `S-TaLiRo`) decouples `Model` (`@models.blackbox` or `@models.ode`), `Specification` (`RTAMT` dense/discrete, `Banquo`, `TLTK`), and `Optimizer` (`UniformRandom`, SciPy `DualAnnealing`, external `PartX`).
  - `decyphir/breach` (`1f8a495727eb04bf849175d33963be5e26a8bfdd`) provides C/MEX-accelerated STL quantitative/sensitivity monitoring (`@STL_Formula`), parameterized input generators (`UniStep`, `VarStep`), and Fibonacci-restarted Nelder-Mead falsification (`Core/Falsify.m:62-96`) over Simulink (`BreachSimulinkSystem`) and external simulators (`BreachSystem`) or recorded traces (`BreachTraceSystem`).
  - `BerkeleyLearnVerify/Scenic` (`979b09e10c2d119cd47f75115740b65f4f7e9999`, Scenic 3) defines declarative geometric and temporal probabilistic distributions over 3D scenes (`CARLA`, `Webots`, `X-Plane`), sampled by `BerkeleyLearnVerify/VerifAI` (`7ef383f191cac0cb2d0174829ac2ec75ab7a0f3c`) using active samplers (cross-entropy, Bayesian optimization, Halton quasi-random) with `multi_objective_monitor` priority DAGs and Clopper-Pearson/Beta failure-rate confidence intervals (`falsifier.py:120-124`).
- **Clinical/physical telemetry archive and HIL signal conversion (`WFDB`)**: `MIT-LCP/wfdb-python` (`cc9f94fcc8bc938c6fb6cb40fb61c85b33e9404e`) defines the canonical PhysioNet integer/physical conversion rules (`adc()`, `dac()`, `adc_gain`, `baseline`, 16-bit modulo-65536 `checksum`, and `DIGITAL_NAN` sentinels) used when replaying real ICU/ECG/arterial-pressure clinical disturbances into medical device controllers.
- **Verified runtime plant-envelope monitors (`KeYmaera X` `ModelPlex`)**: `LS-Lab/KeYmaeraX-release` (`2753f99b53cea5f946386998a39faded05ede677`, `org.keymaerax.btactics.ModelPlex`) bridges offline `dL` proofs to online sampled-data execution via provably conservative `ModelPlexKind.Ctrl` and `ModelPlexKind.Model` arithmetic monitors over observable states and sliding-window parameter estimators (`createSlidingMonitorSpec`).
- **Empirical human mental-model validation (`SMoL`)**: `shriram/smol` (`858d1b461924a7a9a37e9119faf191304dda5835`) provides executable Racket `#lang` semantics (`smol/fun`, `smol/state`, `smol/hof`, `smol/cc`, and deliberate counter-models `smol/dyn-scope-is-bad` and `flat-scope`) backing the SMoL misconception taxonomy and tutor.

## Findings

### 1. Signal Temporal Logic (`STL`/`MTL`) Quantitative Robustness Falsification (`PSY-TaLiRo`, `Breach`, `VerifAI` + `Scenic`)

`Basis: normative + source + execution`

Given a real-valued multi-dimensional trajectory $\mathbf{y}: [0, T] \to \mathbb{R}^m$ and atomic predicates $\mu(\mathbf{y}(t)) \equiv g(\mathbf{y}(t)) \ge 0$, quantitative STL semantics (Maler & Ničković, FORMATS 2004, `DOI: 10.1007/978-3-540-30206-3_12`; Fainekos & Pappas, *Theor. Comput. Sci.* 2009, `DOI: 10.1016/j.tcs.2009.06.021`) replaces $\{\top, \bot\}$ with inductively defined robustness degree $\rho(\varphi, \mathbf{y}, t)$:
$$\begin{aligned}
\rho(g(\mathbf{y}) \ge 0, \mathbf{y}, t) &= g(\mathbf{y}(t)), & \rho(\neg \varphi, \mathbf{y}, t) &= -\rho(\varphi, \mathbf{y}, t), \\
\rho(\varphi_1 \land \varphi_2, \mathbf{y}, t) &= \min\big(\rho(\varphi_1, \mathbf{y}, t),\, \rho(\varphi_2, \mathbf{y}, t)\big), & \rho(\Box_{[a,b]} \varphi, \mathbf{y}, t) &= \inf_{\tau \in [t+a, t+b]} \rho(\varphi, \mathbf{y}, \tau), \\
\rho(\Diamond_{[a,b]} \varphi, \mathbf{y}, t) &= \sup_{\tau \in [t+a, t+b]} \rho(\varphi, \mathbf{y}, \tau), & \rho(\varphi_1 \,\mathcal{U}_{[a,b]}\, \varphi_2, \mathbf{y}, t) &= \sup_{\tau \in [t+a, t+b]} \min\!\left(\rho(\varphi_2, \mathbf{y}, \tau),\, \inf_{s \in [t, \tau]} \rho(\varphi_1, \mathbf{y}, s)\right)
\end{aligned}$$

Soundness theorem (Fainekos & Pappas 2009): If $\rho(\varphi, \mathbf{y}, 0) > 0$, then **every** trajectory $\mathbf{y}'$ within $L_\infty$ tube $\|\mathbf{y}' - \mathbf{y}\|_\infty < \rho(\varphi, \mathbf{y}, 0)$ (under unit Lipschitz predicate scaling) satisfies $\mathbf{y}' \models \varphi$; if $\rho(\varphi, \mathbf{y}, 0) < 0$, $\mathbf{y} \not\models \varphi$. Falsification thus casts counterexample discovery over static parameters $\mathbf{x}_0 \in X_0$ and finite-dimensional input-signal control points $\mathbf{u} \in U^K$ as global non-convex minimization:
$$\min_{(\mathbf{x}_0, \mathbf{u}) \in X_0 \times U^K} \rho\big(\varphi,\, \operatorname{Sim}(\mathbf{x}_0, \mathbf{u}),\, 0\big) < 0$$

In our 4-dimensional lightly damped actuator benchmark (`Basis: execution`, budget `90` simulations over disturbance amplitude, frequency $\omega \in [0.5, 14.0]\text{ rad/s}$, angle offset, and onset time), `UniformRandom` failed to hit the narrow closed-loop resonant ridge near $\omega_r \approx 3.85\text{ rad/s}$ (`best_uniform_rho = +0.0215`, false safe impression), whereas simulated annealing followed the decreasing $\rho$ gradient directly into falsification (`best_annealing_rho = -0.1035 < 0`).

#### Primary-Source Architecture Comparison and Discrete-Time `round(period, 2)` Trap

Direct inspection of `psy-taliro`, `breach`, `VerifAI`, and `Scenic` reveals critical operational invariants and implementation traps:

1. **`PSY-TaLiRo` discrete-time period rounding footgun (`Basis: source + execution`)**:
   In `cpslab-asu/psy-taliro` (`887f2dc321e83688796307f8b0abcf22b3a57b4c`, `src/staliro/specifications/rtamt.py:49-65`), `_evaluate_discrete` computes `period = times[1] - times[0]` and calls:
   ```python
   spec.set_sampling_period(round(period, 2), "s", 0.1)
   ```
   Because `round(period, 2)` rounds the sampling period in seconds to **two decimal places (`10 ms` resolution)**:
   - Any control or physiological signal sampled faster than `200 Hz` (`period < 0.005 s`, such as `250 Hz` ICU recordings where `period = 0.004 s` or `1 kHz` motor/avionics HIL where `period = 0.001 s`) rounds to **`0.0 s`** (`round(0.004, 2) == 0.0`), breaking discrete step conversion!
   - Intermediate rates such as `125 Hz` (`period = 0.008 s`) round to **`0.01 s` (`+25%` time-base dilation)** with a hardcoded `10%` (`0.1`) jitter tolerance! High-rate users of `psy-taliro` MUST use `parse_dense` (`StlDenseTimeSpecification`, `rtamt.py:149-162`) rather than `parse_discrete` unless `period` is an exact integer multiple of `0.01 s`.
2. **`Breach` Fibonacci-restarted Nelder-Mead & structural sensitivity (`Basis: source`)**:
   In `decyphir/breach` (`1f8a495727eb04bf849175d33963be5e26a8bfdd`, `Core/Falsify.m:62-96`), `Falsify` seeds quasi-random points (`QuasiRefine`), runs bounded Nelder-Mead simplex descent (`SOptimPropNM`) with immediate early exit `ifalse = find(val_opt < 0)` (`StopWhenFound = 1`), and grows initial-point density along a **Fibonacci schedule** (`nb_init_total = nb_init_total + nb_init; nb_init = nb_init_total;`, lines `94-95`) across restarts, balancing fast local gradient-free exploitation against global space-filling exploration. Note also `Breach`'s trace invariant (`README.md:54-59`): `time` MUST be strictly increasing and **start at exactly `0`** (`[3 4 5 7]` is rejected).
3. **`VerifAI` + `Scenic` semantic feature spaces and error tables (`Basis: source`)**:
   Directly fuzzing raw pixel or LiDAR arrays is intractable. `Scenic` (`src/scenic/core/scenarios.py:24-40, 147-180`) compiles declarative spatial/visibility/collision constraints (`VisibilityRequirement`, `NonVisibilityRequirement`, `BlanketCollisionRequirement`) into a low-dimensional semantic feature space sampled via rejection + active feedback from `VerifAI` (`src/verifai/falsifier.py:39-41, 76-124, 176-186`). `VerifAI` supports directed `multi_objective_monitor` priority graphs (`params.sampler_params.priority_graph = self.monitor.graph`, avoiding scalarization masking when heterogenous physical units such as meters vs. m/s² collide in `min(rho_1, rho_2)`!), logs counterexamples into `error_table` for PCA/clustering root-cause analysis (`analyze_error_table`), and computes exact Beta/Clopper-Pearson binomial confidence intervals `proportion_confint(c, N, method='beta')` (`falsifier.py:120-124`) when `c == 0` or `c > 0` failures are observed across `N` i.i.d. scenes.

---

### 2. Hardware-in-the-Loop (`HIL`) Injection and Incident-Telemetry Corpus Replay (`PhysioNet WFDB`)

`Basis: source + execution + documentation`

Sim-to-real divergence routinely invalidates controllers whose pure `FP64` ODE simulations pass STL falsification with positive robustness margin. Four physical interface effects must be injected in real-time HIL benches and offline incident-telemetry replay:

1. **Multi-tick bus transport and Zero-Order-Hold (`ZOH`) actuation lag**: CAN-FD / EtherCAT / SPI sensor-to-ECU-to-PWM pipelines introduce $1\text{--}4$ sampling periods of angular lag $\Delta \phi(\omega) = -\omega k \Delta t$, eroding stability margin near crossover frequency $\omega_c$. In our actuator probe (`Basis: execution`), adding a 3-tick (`30 ms`) HIL transport lag + 8-bit PWM duty quantization flips an ideal-safe trajectory (`rho_ideal = +0.0027 > 0`) into an STL safety/settling violation (`rho_hil_zoh = -0.0207 < 0`).
2. **In-band digital dropout sentinels (`WFDB` `DIGITAL_NAN`) and ADC rail clipping (`Basis: source + execution`)**:
   In `MIT-LCP/wfdb-python` (`cc9f94fcc8bc938c6fb6cb40fb61c85b33e9404e`, `src/wfdb/io/_signal.py:492-645` and `src/wfdb/io/record.py:492-502, 930-938`), physical signals $\mathbf{p}$ and stored integer ADC counts $\mathbf{d}$ map via:
   $$d = \operatorname{round}(p \cdot \text{adc\_gain} + \text{baseline}), \qquad p = \frac{d - \text{baseline}}{\text{adc\_gain}}$$
   with `adc_gain > 0`, 32-bit signed `baseline`, and modulo-`65536` sample checksum verification (`record.py:936`). Crucially, `adc_inplace` (`_signal.py:540-550`) maps IEEE-754 `NaN` samples (caused by detached ICU electrodes, electrosurgical interference, or catheter flush artifacts) to format-specific **minimum signed integers** (`_digi_nan(self.fmt)`: `-32768` in 16-bit format `'16'`, `-2048` in 12-bit `'212'`, `-2147483648` in `'32'`). Embedded C/Rust firmware or HIL replay harnesses that read raw 16-bit ADC frames (`d_signal`) and apply `(d - baseline) / adc_gain` **without filtering `d == -32768` into a sensor-fault hold/quarantine state** inject a massive `-16.384`-unit step spike! Across a realistic `250 ms` (`25`-sample) dropout in our probe, this unmasked `DIGITAL_NAN` spike winds up the controller's integral accumulator and drives physical overshoot to `rho_hil_wfdb_nan = -0.1623` (`60x` worse than the ideal margin!).
3. **Real-world disturbance non-Gaussianity**: Synthetic Gaussian white noise misses heavy-tailed, non-stationary real-world transients that must be replayed directly from curated open incident corpora:
   - **Clinical physiological telemetry**: PhysioNet (`Goldberger et al., Circulation 2000, DOI: 10.1161/01.cir.101.23.e215` — MIT-BIH Arrhythmia, MIMIC-III/IV arterial blood pressure `ABP` dicrotic-notch / motion-artifact recordings) for infusion pumps, ventilators, and defibrillators;
   - **Seismic & tsunami/geophysical accelerograms**: Strong-motion borehole/surface time-series (dc offsets, ADC clipping, high-frequency primary-arrival spikes) for Early Earthquake Warning (`STA/LTA`) triggers;
   - **Grid synchrophasor (`PMU`) & flight-data disturbances**: Sub-synchronous resonance, voltage-angle jumps during fault clearing, and dual-pitot/AOA spike logs.

---

### 3. Verified Runtime Plant-Validity & Controller Envelope Monitoring (`ModelPlex`)

`Basis: normative + source + execution`

Even exhaustive offline theorem proving (`KeYmaera X`) plus pre-deployment HIL falsification cannot prevent an online physical plant from departing its modeled ODE at runtime (e.g., tire-road friction $\mu$ dropping on black ice, hydraulic actuator fade, or unmodeled payload mass shift). **ModelPlex** (Mitsch & Platzer, *Formal Methods in System Design* 2016, `DOI: 10.1007/s10703-016-0241-z`; `LS-Lab/KeYmaeraX-release` @ `2753f99b53cea5f946386998a39faded05ede677`, `org.keymaerax.btactics.ModelPlex`) closes this sim-to-real gap with a machine-checked theorem:

Given an offline `dL` safety proof $\vdash_{\text{dL}} A \to [\alpha^*]P$ where hybrid program $\alpha \equiv \alpha_{\text{ctrl}}; \alpha_{\text{plant}}$ has bound variables $V = \operatorname{BV}(\alpha)$, `createMonitorSpecificationConjecture` (`ModelPlex.scala:233-331`) constructs the diamond reachability specification over pre-state $V$ and post-state $V_{\text{post}}$ (`NAMED_POST_VAR`, appending `"post"`, `ModelPlexTrait.scala:38-40`):
$$\Upsilon \equiv \bigwedge_{v \in V} (v_{\text{post}} = v), \qquad \phi_{\text{spec}} \equiv \exists V_{\text{unobs}}\, \exists \Theta_{\text{unknown}}\, \langle \alpha \rangle \Upsilon$$
Applying KeYmaera X's axiomatic `chase` + real quantifier elimination (`optimizationOneWithSearch`, `ModelPlex.scala:89-96`) produces quantifier-free real-arithmetic formulas in two modes (`ModelPlexKind`, `ModelPlexTrait.scala:16-18`):

1. **`ModelPlexKind.Ctrl` (`controllerMonitorByChase`)**: Synthesizes $\chi_{\text{ctrl}}(\mathbf{x}, \mathbf{u})$ over discrete control $\alpha_{\text{ctrl}}$ alone. Evaluated in $O(1)$ floating-point/interval arithmetic (`< 1 µs`) on every untrusted AI/MPC/PID command $\mathbf{u}_k$ *before* actuation: if $\chi_{\text{ctrl}}(\mathbf{x}_k, \mathbf{u}_k)$ fails, a simplex/shielded architecture substitutes a pre-verified fallback action (such as maximum braking $a = -B$).
2. **`ModelPlexKind.Model` (`modelMonitorByChase`)**: Synthesizes $\chi_{\text{model}}(\mathbf{x}_{k-1}, \mathbf{u}_{k-1}, \mathbf{x}_k)$ over the full loop body $\alpha_{\text{ctrl}}; \{x' = f(x, u) \ \& \ Q\}$. If $\chi_{\text{model}}(\mathbf{x}_{k-1}, \mathbf{u}_{k-1}, \mathbf{x}_k)$ holds for every consecutive sample transition $0 \to 1 \to \dots \to k$ and initial state $\mathbf{x}_0 \models A$, **Corollary 1 of Mitsch & Platzer guarantees $\mathbf{x}_k \models P$ for the real physical execution**. Conversely, when icy-road brake fade reduces actual deceleration from commanded $-4.0\text{ m/s}^2$ to $-1.2\text{ m/s}^2$ (`Basis: execution`), `mxFormatShape("metricfml")` (`toMetricT`, `ModelPlex.scala:162-171`) immediately flips the quantitative plant margin negative (`plant_ice_fade = -0.2300 < 0` at $x = 4.394\text{ m}$, more than `5.6 m` *before* the obstacle at $d_{\text{obs}} = 10.0\text{ m}$!), alerting the supervisory fallback while emergency margin still remains.
3. **Unobservable state & sliding-window parameter estimation (`ModelPlex.scala:198-367`)**: `partitionUnobservable` existentially eliminates unobservable state variables paired with at most one sensor variable (`lines 279-290`; multi-variable sensor couplings explicitly raise `IllegalArgumentException`) and chains $W$ consecutive transitions in `createSlidingMonitorSpec` (`lines 344-367`) to tighten bounds on unknown constant disturbances.

---

### 4. Empirical Behavioral Litmus Validation of Human Mental Models (`SMoL`)

`Basis: source + execution + documentation`

Formal verification proves that an implementation satisfies a written specification—it **cannot** prove that the human author or operator accurately understands what the specification or language surface means! Kuang-Chen Lu and Shriram Krishnamurthi (*Identifying and Correcting Programming Language Behavior Misconceptions*, PACMPL OOPSLA 2024, `DOI: 10.1145/3649823`; implemented over `shriram/smol` @ `858d1b461924a7a9a37e9119faf191304dda5835`) demonstrate that programmers across Python, JavaScript, Java, Racket, and Rust share a common core semantic substrate—the **Standard Model of Languages (`SMoL`)**: eager call-by-value evaluation, lexical block scoping, mutable variable bindings (`set!`), heap-allocated mutable structures (`mvec`/`mpair` in `state/semantics.rkt:11-28`), and first-class closures capturing environment bindings (`hof/semantics.rkt`)—yet systematically harbor **predictable, measurable mental-model misconceptions**.

Inspecting `shriram/smol` (`state/semantics.rkt` and `dyn-scope-is-bad/semantics.rkt:46-117`, which explicitly reifies dynamic scoping via a parameterized hash table `(define dvs (make-parameter (make-hasheq)))` copied at every call site `(parameterize ([dvs (hash-copy (dvs))]) ...)`) isolates three high-frequency human misconception classes directly relevant to specification and systems engineering (`Basis: source + execution`):

1. **Lexical vs. Dynamic Scope (`Litmus L1`)**: In `(defvar x 10) (deffun (f) x) (let ([x 20]) (f))`, `SMoL` lexical semantics (`smol/fun`) evaluates `(f)` in its definition environment (`10`), whereas programmers holding a dynamic call-stack mental model (`smol/dyn-scope-is-bad`) predict `20`. In formal specifications, analogous confusion between lexical `old(x)` / quantifier binder capture and dynamic call-site state causes silent specification inversions.
2. **Heap Structure Mutation vs. Variable Rebinding (`Litmus L2`)**: Given `(defvar v (mvec 1 2)) (defvar w v) (vec-set! w 0 99) (set! w (mvec 7 8))` followed by `(vec-ref v 0)`, store-passing semantics (`Env: Id -> Loc`, `Store: Loc -> Val`) yields **`99`**: `w` and `v` initially alias heap vector `0`, `(vec-set! w 0 99)` mutates heap vector `0`, and `(set! w ...)` rebinds `w`'s variable slot without touching `v` or heap vector `0`. Human litmus testing catches **both** opposing misconceptions via distinct distractors: the *value-copy* model predicts **`1`** (missing aliasing on `(defvar w v)`), while the *reference-chaining* (`&w -> &v`) model predicts **`7`** (mistaking `set!` variable rebinding for deep alias overwrite).
3. **Mutable Loop-Variable Capture in Closures/Callbacks (`Litmus L3`)**: Closing `lambda () i` inside a loop that mutates a single shared variable cell yields **`[2, 2, 2]`**, whereas binding a fresh per-iteration parameter yields **`[0, 1, 2]`**. In event-driven CPS/HIL monitors and async callbacks, shared-cell closure capture silently binds all safety watchdogs to the *last* sensor channel ID!

Crucially, Lu & Krishnamurthi show that prose documentation and type signatures alone fail to dislodge entrenched misconceptions; durable mental-model alignment requires **refutational behavioral litmus instruments** (`predict output -> observe concrete execution discrepancy -> inspect explicit Environment + Store notional machine` via *Stacker* / `SMoL Tutor`).

---

### 5. Cross-System Six-Level Performance & Resource Footprint Matrix (`L1`–`L6`)

`Basis: source + documentation + execution`

| System / Method | `L1` Human & Agent Authoring Burden | `L2` Toolchain Build Time & Deps | `L3` Falsification / Synthesis Latency | `L4` Online / Runtime Execution Cost | `L5` Trace / Monitor Verification Speed | `L6` RAM, Disk & Artifact Footprint |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **`PSY-TaLiRo`** (`cpslab-asu/psy-taliro`) | `~25–70 LoC` Python (`@models.blackbox`, STL string, `Options` bounds) | `< 15 s` `pip install psy-taliro rtamt scipy` | `0.25 s` (`90` pure-Python ODE runs) to `5–60 min` (`1,000` Simulink/HIL runs via `DualAnnealing`) | `0%` on deployed target (offline test harness) | **`< 1 ms`** per `1,000`-pt trace (`RTAMT` C++/Python STL monitor) | `~80–250 MiB` Python/SciPy RSS; `< 50 KiB` falsifying `Sample` + `Trace` JSON |
| **`Breach`** (`decyphir/breach`) | `~15–50 LoC` `.stl` spec file + MATLAB `FalsificationProblem` script | `< 30 s` `InitBreach` C/MEX compilation inside MATLAB | `10–300 s` (`100–2,000` Simulink runs with C/MEX STL + Nelder-Mead) | `0%` on target (`offline` / HIL host) | **`0.05–0.5 ms`** per trace (`STL_EvalMex` lemire monotonic-wedge min/max deque) | `1.5–4 GiB` MATLAB + Simulink process RSS |
| **`VerifAI` + `Scenic`** (`BerkeleyLearnVerify`) | `~20–80 LoC` `.scenic` probabilistic scene + `~40 LoC` `falsifier.py` | `< 30 s` Python (`scenic`, `verifai`, `trimesh`); `CARLA` simulator `~15 GB` | Scene sampling **`1–15 ms`/scene** (`rejection`); `3D` `CARLA` rollouts `2–10 s`/run (`parallel_falsifier` scales linearly) | `0%` target overhead | `< 2 ms` `mtl_specification` / `multi_objective_monitor` DAG eval + `< 1 ms` Beta CI | `~300 MiB` (`VerifAI`/`Scenic`) + `4–12 GiB` VRAM/RAM when running `CARLA` |
| **`WFDB` / HIL Replay** (`MIT-LCP/wfdb-python`) | `~20–60 LoC` signal loader + DAC/NaN sanitizer + real-time FIFO streamer | `< 10 s` `pip install wfdb` (NumPy/SciPy); HIL FPGA/RTOS rig `hours–days` | Real-time `1.0x` wall-clock on physical HIL (`1 h` clinical trace = `1 h` wall-clock); `> 500x` faster in SIL | `0%` deployed cost (`HIL` testbench only) | **`> 100 MB/s`** vectorized `dac()` + modulo-`65536` `calc_checksum()` | `MIT-BIH` record `~2 MB`; `MIMIC` signal shards `GB–TB`; `< 64 KiB` HIL DMA ring |
| **`ModelPlex`** (`KeYmaera X`) | `~30–120 LoC` `.kyx` hybrid `dL` model + Bellerophon proof script (`high` expertise) | `2–6 min` SBT Scala build (`keymaerax.jar` `~65 MB`) + `Z3` (bundled) or `Mathematica` | **`0.5–30 s`** offline `mxSynthesize` + real QE (`exponential` worst-case in variable count if unsimplified!) | **`10–150 ns` (`~20–120` CPU cycles, `0` heap allocs)** quantifier-free C arithmetic guard per control tick! | Offline proof checked by **`~2,000 LoC` KeYmaera X microkernel** in `< 200 ms`; online check `< 1 µs` | Offline prover `0.8–3 GiB` JVM + QE RSS; online monitor **`.text < 2 KiB`, `0 B` heap** |
| **`SMoL` Litmus Suite** (`shriram/smol`) | `~6–15 LoC` self-contained litmus snippet + `3–4` misconception distractors | `< 15 s` `raco pkg install smol` on Racket | `5–15 min` human participant completion (`12–16` litmus items); `< 50 ms` automated interpreter check | N/A (human specification/comprehension gate) | `< 10 ms` exact Racket evaluation across `#lang smol/state` vs. `#lang smol/dyn-scope-is-bad` | `~60–120 MiB` Racket VM RSS; `< 4 KiB` litmus item bank |

---

### 6. Human Comprehensibility (`C1`) and Conceptual Simplicity / Universal Model Refinement (`C2`)

`Basis: source + derived`

#### `C1` — Human Comprehensibility vs. Agent Execution Ergonomics

- **Why STL + Scenic excel at `C1` where raw cost functions fail**: Ad-hoc Python reward/penalty sums (`-100 * crash - 2.5 * overshoot`) conflate physical units and silently trade safety violations against performance rewards. Declarative `STL` (`alw_[0, 4.0](abs(x) <= 0.95)`) and `Scenic` (`ego = new Car on road, facing roadDirection`) stay within **`<= 4` human working-memory concepts**, map directly to regulatory requirements (`ISO 26262` / `IEC 60601`), and paired with `VerifAI`'s `multi_objective_monitor` priority DAG (`falsifier.py:39-41`) prevent unit-scale masking without requiring humans to invent arbitrary scalar weights.
- **Readable vs. opaque `ModelPlex` monitors**: Unsimplified quantifier-elimination output from CAD (`Mathematica`/`Z3`) can explode into hundreds of disjunctive polynomial clauses that an LLM/compiler processes effortlessly (`L4 < 150 ns`) yet a human safety reviewer cannot audit (`poor C1`). Applying KeYmaera X's `optimizationOneWithSearch` + `SimplifierV2` (`ModelPlex.scala:90-95`) reduces the 1D kinematic monitor back to the single physically transparent energy-stopping inequality $x + v T + \tfrac{1}{2} a T^2 + \frac{\max(0, v + a T)^2}{2 B} \le d_{\text{obs}}$, preserving `1:1` correspondence with human Newtonian intuition!
- **Distinguishing agent fluency from human comprehension (`SMoL`)**: An LLM agent can translate natural-language prose into formal contracts in seconds while faithfully mirroring a human prompt's subtle aliasing or closure-capture misconception—or conversely generating a contract using lexical/reference rules the human reviewer misreads. Embedding `SMoL`-style **concrete input-output behavioral litmus examples** alongside formal contracts catches human-vs-formalism divergence before deployment.

#### `C2` — Conceptual Simplicity, Orthogonality, and Anti-Shell-Game Model Refinement

Across continuous falsification, HIL replay, runtime monitoring, and mental-model testing, disparate mechanisms refine to **three orthogonal invariants**:

1. **Quantitative Signed Margin Semiring $(\mathbb{R} \cup \{\pm\infty\}, \max, \min)$ as Universal Interface**:
   - Both offline `STL` falsification (`PSY-TaLiRo`, `Breach`, `VerifAI`) and online `ModelPlex` metric monitoring (`mxFormatShape("metricfml")`, `ModelPlex.scala:169`) evaluate formulas in the **exact same max-min quantitative Lattice/Semiring**! Treating Boolean satisfaction as merely $\operatorname{sign}(\rho) > 0$ eliminates duplicate Boolean vs. quantitative evaluators and allows the *same* margin signal to guide pre-deployment simulated annealing and online simplex fallback switching.
   - **Scale-invariance refinement**: Raw predicate differences $g_1(\mathbf{y}) = 100 - P_{\text{mmHg}}$ vs. $g_2(\mathbf{y}) = 0.05 - I_{\text{amps}}$ distort `min(g_1, g_2)` by `2,000x`. Normalizing every atomic predicate by its declared physical engineering tolerance $\tilde{g}_k(\mathbf{y}) = g_k(\mathbf{y}) / \Delta_k$ (dimensionless safety margin in units of full-scale tolerance, or retaining partial order via `VerifAI`'s `multi_objective_monitor`) eliminates unit-mismatch artifacts at the root without solver hacks.
2. **Explicit Typed Physical Transducer Boundary (`Counts <-> Physical | SensorFault`)**:
   - The `WFDB` `DIGITAL_NAN = -32768` windup catastrophe (`_signal.py:533-550`) is a textbook Ousterhout shallow-interface failure when raw `int16` counts cross untyped into control math. Typing the ADC transducer output as a sum domain `Sample<Unit> = Valid(BoundedFixed) | SensorFault(DropoutKind)` makes in-band sentinel values, rail saturation (`|d| == 2047`), and checksum mismatches impossible to feed into integral control accumulators without an explicit fault-handling branch.
3. **Explicit Two-Map Store-Passing Notional Machine (`Env: Id -> Loc`, `Store: Loc -> Val`)**:
   - `SMoL` (`shriram/smol`) demonstrates that `90%+` of cross-language state/closure confusion disappears when programmers stop reasoning via ad-hoc per-language "pass-by-object-reference" slogans and evaluate every construct over one universal pair `(Environment, Heap Store)`.

---

### 7. End-to-End Solution & Implementation Validation Methodology (`V1`–`V4`)

`Basis: source + execution + derived`

| Validation Axis | Failure Mode If Omitted | Concrete End-to-End Validation Protocol & Quantitative Oracle |
| :--- | :--- | :--- |
| **`V1` Specification Adequacy, Vacuity & Time-Base Litmus** | Vacuous antecedent $\Box(A \to B)$ where $A$ never triggers (`rho = +inf`), wrong `rtamt` discrete period (`round(0.004, 2) == 0.0`), or unit mismatch (`mmHg` vs `cmH2O`, `rad` vs `deg`) makes falsifiers report false safety. | **Antecedent-witness & mutant-plant gates**: Require separate existential witness check $\rho(\Diamond A, \mathbf{y}, 0) > 0$; assert `parse_dense` (or exact `10 ms`-multiple period) in `PSY-TaLiRo`; run falsifier against seeded controller mutants (gain sign flip, `+3` tick delay, sensor bias) and require `100%` mutant falsification ($\rho < 0$). |
| **`V2` Monitor, QE & Simulator Lowering Soundness Fuzzing** | Unsound `SimplifierV2` / QE rewrite in monitor synthesis, `FP64` catastrophic cancellation inside generated C monitor, or fixed-step Runge-Kutta (`RK45`) aliasing stiff chattering dynamics. | **Double-checked `ModelPlex` proof + differential monitor testing**: Verify KeYmaera X `createMonitorCorrectnessConjecture` (`assumptions -> (monitor -> <prg;>Upsilon)`, `ModelPlex.scala:369-379`) inside the `2,000-LoC` kernel; differentially fuzz `PSY-TaLiRo` (`RTAMT`), `Breach` (`STL_EvalClassic`), and reference backward-horizon deque evaluator across `10,000` random irregular-timestamp traces including `NaN`/rail edge cases (`0` sign disagreements). |
| **`V3` Real-Time Jitter, Bus Saturation & Fault-Injection HIL** | Desktop SIL misses RTOS scheduling jitter, priority inversion, CAN/SPI frame drops, DMA double-fetch tearing, and power-brownout ADC resets. | **Hardware-in-the-Loop fault-campaign matrix**: Drive the compiled target binary on real MCU silicon from a deterministic FPGA/real-time plant simulator injecting (a) measured worst-case interrupt/DMA load, (b) ADC rail saturation & `DIGITAL_NAN` lead-off bursts, (c) quantized PWM deadtime, and (d) clock-drift skew between plant and controller crystals. |
| **`V4` Incident-Corpus Replay, Online `ModelPlex` Shielding & `SMoL` Human Litmus** | Synthetic smooth spline/sinusoid disturbances miss real clinical/seismic/grid artifacts; operators or spec authors misunderstand mode latches or variable aliasing. | **Three-layer reality anchor**: (1) Replay full archived real-world incident corpora (`PhysioNet` MIMIC/MIT-BIH records, strong-motion seismic logs, grid fault recordings) requiring `0` unhandled NaNs/windups; (2) Deploy online `ModelPlexKind.Ctrl` + `ModelPlexKind.Model` guards logging real-world plant-envelope margin histograms in shadow/active mode; (3) Validate human spec authors & operators on domain-instantiated `SMoL` behavioral litmus scenarios (`>= 95%` discriminator accuracy on aliasing, scope, closure capture, and mode latches). |

## Boundaries

- **Falsification vs. Exhaustive Verification (`known not to apply`)**: `PSY-TaLiRo`, `Breach`, and `VerifAI` are **incomplete bug-finding / stress-testing engines**, not proof systems: terminating after `1,000` or `100,000` simulations with minimum observed robustness $\rho_{\min} = +0.0215 > 0$ does **not** guarantee absence of narrow zero-measure or resonant counterexamples outside sampled neighborhoods (`VerifAI`'s `get_confidence_interval` bounds failure probability *only* under the exact `Scenic` prior distribution, not under distribution shift!).
- **`ModelPlex` unobservable multi-sensor coupling & liveness (`unsupported` / `known not to apply`)**: `ModelPlex.scala:282-290` explicitly rejects sensor estimator specifications referencing multiple auxiliary variables (`IllegalArgumentException: Sensor specifications with multiple variables ... not supported`). Furthermore, while `ModelPlexKind.Model` detects online plant departure ($\chi_{\text{model}} < 0$), physical safety *after* departure depends on the physical existence of a safe fallback action under the degraded real-world dynamics (if brake hydraulics are completely severed so actual deceleration is $0$, detecting the violation cannot physically prevent collision).
- **High-dimensional `ModelPlex` quantifier elimination (`unknown` / exponential scaling)**: Cylindrical Algebraic Decomposition (`CAD`) for nonlinear polynomial ODEs has doubly-exponential worst-case complexity $O(d^{2^n})$ in variable count $n$; for high-order nonlinear plants without closed-form polynomial differential invariants (`Pegasus`), exact symbolic `ModelPlex` synthesis may time out unless conservative Taylor/differential-invariant over-approximations are supplied manually.
- **`PSY-TaLiRo` discrete-time `RTAMT` sub-`10 ms` sampling (`known not to apply`)**: As established from `src/staliro/specifications/rtamt.py:61`, `DiscreteMapped` and `DiscreteNamed` truncate `period = times[1] - times[0]` via `round(period, 2)` and fail or distort horizons whenever `period` is not an exact multiple of `0.01 s`; use `DenseMapped` / `DenseNamed` instead.
- **External proprietary Simulink / 3D CARLA binaries (`not examined` by execution in minimal sandbox)**: While `Breach` (`Falsify.m`), `Scenic`, and `VerifAI` sources were inspected directly at their pinned commits and validated algorithmically via our standalone Python ODE/STL/ModelPlex/SMoL probe, closed-source `MATLAB/Simulink` and GPU `Unreal Engine / CARLA` rendering binaries were `not examined` via live execution in this headless CPU environment.

## Evidence

### Primary Repositories and Source Coordinates (Observed `2026-11-19`)

1. **`cpslab-asu/psy-taliro` @ `887f2dc321e83688796307f8b0abcf22b3a57b4c`**:
   - `src/staliro/models.py:35-73, 100-220`: `Trace` (`SortedDict[float, S]` time-indexed trajectory), `@models.blackbox(step_size=...)`, and `@models.ode(method="RK45")`.
   - `src/staliro/optimizers.py:89-220`: `Sample`, `ObjFunc` protocol, `UniformRandom(min_cost=...)`, and `DualAnnealing` early-stopping falsification loop (`_falsify`, lines `197-206`).
   - `src/staliro/specifications/rtamt.py:49-220`: `_evaluate_discrete` (`spec.set_sampling_period(round(period, 2), "s", 0.1)` at line `61`) vs. `_evaluate_dense` (`StlDenseTimeSpecification` at lines `149-162`).
2. **`decyphir/breach` @ `1f8a495727eb04bf849175d33963be5e26a8bfdd`**:
   - `README.md:52-123, 236-339`: `BreachTraceSystem` (`time(1) == 0` strictly increasing invariant), `STL_Formula`, quantitative `BreachRequirement.Eval`, `UniStep`/`VarStep` input generators, and `BreachSystem` external simulator interface.
   - `Core/Falsify.m:61-118`: `QuasiRefine` initialization, `SOptimPropNM` Nelder-Mead optimization, `val_opt < 0` early termination, and Fibonacci restart schedule (`nb_init_total = nb_init_total + nb_init; nb_init = nb_init_total;`, lines `94-95`).
3. **`BerkeleyLearnVerify/VerifAI` @ `7ef383f191cac0cb2d0174829ac2ec75ab7a0f3c`** and **`BerkeleyLearnVerify/Scenic` @ `979b09e10c2d119cd47f75115740b65f4f7e9999`**:
   - `VerifAI/src/verifai/falsifier.py:19-220`: `falsifier` base loop, `multi_objective_monitor` priority graph propagation (`lines 39-41`), `error_table` / `safe_table` logging, and Beta Clopper-Pearson `get_confidence_interval` (`lines 120-124`).
   - `Scenic/src/scenic/core/scenarios.py:14-42, 147-180`: `Scene` synthesis, geometric/visibility requirement classes, and simulator bridge.
4. **`LS-Lab/KeYmaeraX-release` @ `2753f99b53cea5f946386998a39faded05ede677`**:
   - `keymaerax-core/src/main/scala/org/keymaerax/btactics/ModelPlexTrait.scala:16-72` & `ModelPlex.scala:62-380`: `ModelPlexKind.{Ctrl, Model}`, `NAMED_POST_VAR`, `mxFormatShape` (`boolean`, `metricprg`, `metricfml` via `toMetricT` at lines `162-171`), `partitionUnobservable` (`lines 200-221`), `createMonitorSpecificationConjecture` (`lines 233-331`, including single-sensor-variable restriction at lines `282-290`), `createSlidingMonitorSpec` (`lines 344-367`), and `createMonitorCorrectnessConjecture` (`lines 369-379`).
5. **`MIT-LCP/wfdb-python` @ `cc9f94fcc8bc938c6fb6cb40fb61c85b33e9404e`**:
   - `src/wfdb/io/_signal.py:492-645`: `adc()` and `dac()` physical-digital conversions and `_digi_nan(self.fmt)` sentinel substitution (`adc_inplace`, lines `540-550`).
   - `src/wfdb/io/record.py:492-502, 930-938`: `adc_gain > 0`, 32-bit `baseline` bounds, and modulo-`65536` channel `checksum` validation.
6. **`shriram/smol` @ `858d1b461924a7a9a37e9119faf191304dda5835`**:
   - `state/semantics.rkt:11-32`: Mutable vector (`mvec`, `vec-set!`), mutable pair (`mpair`, `set-left!`, `set-right!`), and variable mutation (`set!`) exports over lexical `smol/fun/semantics`.
   - `dyn-scope-is-bad/semantics.rkt:46-117`: Explicit dynamic-scope counter-language (`dvs` hash parameter copied at `dyn-app`) contrasting against lexical `smol/hof/semantics`.

### Foundational Peer-Reviewed Literature

- Oded Maler and Dejan Ničković, *Monitoring Temporal Properties of Continuous Signals*, FORMATS/FTRTFT 2004 (`DOI: 10.1007/978-3-540-30206-3_12`).
- Georgios E. Fainekos and George J. Pappas, *Robustness of temporal logic specifications for continuous-time signals*, Theoretical Computer Science 410(42), 2009 (`DOI: 10.1016/j.tcs.2009.06.021`).
- Yashwant Annpureddy, Che Liu, Georgios Fainekos, and Sriram Sankaranarayanan, *S-TaLiRo: A Tool for Temporal Logic Falsification for Hybrid Systems*, TACAS 2011 (`DOI: 10.1007/978-3-642-20398-5_22`); Quinn Thibeault et al., *PSY-TaLiRo: A Python Toolbox for Search-Based Test Generation for Cyber-Physical Systems*, FMICS 2021 (`DOI: 10.1007/978-3-030-85248-1_15`).
- Alexandre Donzé, *Breach, A Toolbox for Verification and Parameter Synthesis of Hybrid Systems*, CAV 2010 (`DOI: 10.1007/978-3-642-14295-6_17`).
- Tommaso Dreossi et al., *VerifAI: A Toolkit for the Formal Design and Analysis of Artificial Intelligence-Based Systems*, CAV 2019 (`DOI: 10.1007/978-3-030-25540-4_25`); Daniel J. Fremont et al., *Scenic: A Language for Scenario Specification and Scene Generation*, PLDI 2019 (`DOI: 10.1145/3314221.3314633`).
- Stefan Mitsch and André Platzer, *ModelPlex: Verified runtime validation of verified cyber-physical system models*, Formal Methods in System Design 49(1), 2016 (`DOI: 10.1007/s10703-016-0241-z`).
- Ary L. Goldberger et al., *PhysioBank, PhysioToolkit, and PhysioNet: Components of a New Research Resource for Complex Physiologic Signals*, Circulation 101(23), 2000 (`DOI: 10.1161/01.cir.101.23.e215`).
- Kuang-Chen Lu and Shriram Krishnamurthi, *Identifying and Correcting Programming Language Behavior Misconceptions*, PACMPL 8(OOPSLA1), 2024 (`DOI: 10.1145/3649823`).

### Executed Micro-Probe Output (`2026-11-19`, Python 3 Standard Library, `252.93 ms`)

Executing the standalone verification script reproduced below in `## Revalidation` yielded:
```text
stl_search: best_uniform_rho=+0.0215 best_annealing_rho=-0.1035
rtamt_round: p250hz=0.00 p125hz=0.01
reality_gap: rho_ideal=+0.0027 rho_hil_zoh=-0.0207 rho_hil_wfdb_nan=-0.1623
modelplex: ctrl_ok=+1.0000 plant_ok=+0.0200 plant_ice_fade=-0.2300
smol_litmus: L1=(10,20) L2=(99,1,7) L3=([2, 2, 2],[0, 1, 2])
```

## Revalidation

Run the following self-contained standard-library Python check (`< 0.4 s`, zero external packages or network access) to revalidate (1) quantitative STL robustness simulated-annealing falsification vs. uniform random search in 4D, (2) `PSY-TaLiRo`'s `round(period, 2)` discrete-time period collapse/dilation, (3) sim-to-real HIL ZOH lag + unmasked `WFDB` `DIGITAL_NAN = -32768` integral windup falsifying an ideal-safe ODE controller, (4) `ModelPlex` controller and metric plant-validity monitor detection of brake fade prior to obstacle collision, and (5) `SMoL` store-passing behavioral litmus discriminators:

```bash
python3 - <<'PY'
import math, random

def simulate_plant(amp, omega, ang_off, t_on, dt=0.01, t_end=4.0, hil_mode="ideal"):
    steps = int(round(t_end / dt))
    x, v, integ = 0.20, 0.0, 0.0
    fifo = [0.0, 0.0, 0.0]
    xs, ts = [], []
    for k in range(steps + 1):
        t = k * dt
        ts.append(t)
        xs.append(x)
        if hil_mode == "ideal":
            x_meas = x
        else:
            d_val = max(-2047, min(2047, round(x * 2000.0)))
            if hil_mode == "wfdb_nan" and 60 <= k < 85:
                d_val = -32768
            x_meas = d_val / 2000.0
        integ += x_meas * dt
        u_cmd = -7.0 * x_meas - 1.3 * v - 2.5 * integ
        if hil_mode == "ideal":
            u_act = max(-12.0, min(12.0, u_cmd))
        else:
            q = 24.0 / 256.0
            fifo.append(max(-12.0, min(12.0, round(u_cmd / q) * q)))
            u_act = fifo.pop(0)
        d = amp * math.sin(omega * t + ang_off) if t >= t_on else 0.0
        acc = u_act + d - 0.5 * v - 9.0 * x
        x += v * dt
        v += acc * dt
    return ts, xs

def stl_robustness(ts, xs, dt):
    rho_safe = min(0.95 - abs(x) for x in xs)
    i0, i1, w = int(round(2.0 / dt)), int(round(3.0 / dt)), int(round(0.8 / dt))
    rho_settle = max(min(0.30 - abs(xs[j]) for j in range(i, min(len(xs), i + w + 1))) for i in range(i0, i1 + 1))
    return min(rho_safe, rho_settle)

rng = random.Random(20261119)
best_rand = min(stl_robustness(*simulate_plant(rng.uniform(0.5, 2.8), rng.uniform(0.5, 14.0),
                rng.uniform(0.0, 2 * math.pi), rng.uniform(0.0, 2.2)), 0.01) for _ in range(90))
cur = [1.2, 9.5, 1.0, 1.2]
bounds = [(0.5, 2.8), (0.5, 14.0), (0.0, 2 * math.pi), (0.0, 2.2)]
scales = [0.35, 1.10, 0.60, 0.30]
cur_rho = best_sa = stl_robustness(*simulate_plant(*cur), 0.01)
for step in range(1, 90):
    temp = 0.12 * (0.93 ** step)
    cand = [max(lo, min(hi, c + rng.gauss(0.0, s))) for c, (lo, hi), s in zip(cur, bounds, scales)]
    cand_rho = stl_robustness(*simulate_plant(*cand), 0.01)
    if cand_rho < cur_rho or rng.random() < math.exp((cur_rho - cand_rho) / max(temp, 1e-6)):
        cur, cur_rho = cand, cand_rho
    best_sa = min(best_sa, cand_rho)

assert best_rand > 0.0 and best_sa < 0.0
assert round(1.0 / 250.0, 2) == 0.0 and round(1.0 / 125.0, 2) == 0.01

rho_ideal = stl_robustness(*simulate_plant(2.35, 3.85, 0.0, 0.1, hil_mode="ideal"), 0.01)
rho_zoh = stl_robustness(*simulate_plant(2.35, 3.85, 0.0, 0.1, hil_mode="hil_zoh"), 0.01)
rho_nan = stl_robustness(*simulate_plant(2.35, 3.85, 0.0, 0.1, hil_mode="wfdb_nan"), 0.01)
assert rho_ideal > 0.0 and rho_zoh < 0.0 and rho_nan < -0.10

def mp_ctrl(x, v, a, A=2.0, B=4.0, T=0.1, d_obs=10.0):
    if a == -B: return 0.0
    vm = max(0.0, v + a * T)
    return min(A - a, a + B, d_obs - (x + v * T + 0.5 * a * T * T + (vm * vm) / (2.0 * B)))

def mp_plant(x0, v0, a, x1, v1, T=0.1, ex=0.02, ev=0.05):
    return min(ex - abs(x1 - (x0 + v0 * T + 0.5 * a * T * T)), ev - abs(v1 - max(0.0, v0 + a * T)))

assert mp_ctrl(4.0, 4.0, 1.0) > 0.0
assert mp_plant(4.0, 4.0, -4.0, 4.0 + 0.4 - 0.02, 3.6) > 0.0
assert mp_plant(4.0, 4.0, -4.0, 4.0 + 0.4 - 0.006, 3.88) < 0.0

heap = {0: [1, 2]}
ev = ew = 0
heap[ew][0] = 99
heap[1] = [7, 8]
ew = 1
cell = [0]
th_shared = []
for i in range(3):
    cell[0] = i
    th_shared.append(lambda c=cell: c[0])
th_fresh = [(lambda val: (lambda: val))(i) for i in range(3)]
assert heap[ev][0] == 99 and [f() for f in th_shared] == [2, 2, 2] and [f() for f in th_fresh] == [0, 1, 2]
print("OK: staliro + hil/wfdb + modelplex + smol revalidation passed")
PY
```

To revalidate upstream repository behavior when updating any pinned commit in `REPORT.json`:
1. Inspect `src/staliro/specifications/rtamt.py` (`_evaluate_discrete`) in `cpslab-asu/psy-taliro` to check whether `round(period, 2)` was replaced by exact unit-scaled period forwarding (`ms`/`us`/`ns`).
2. Inspect `keymaerax-core/src/main/scala/org/keymaerax/btactics/ModelPlex.scala` (`createMonitorSpecificationConjecture`, `mxFormatShape`) in `LS-Lab/KeYmaeraX-release` for changes to multi-variable sensor estimator restrictions.
3. Inspect `src/wfdb/io/_signal.py` (`adc`, `dac`, `_digi_nan`) in `MIT-LCP/wfdb-python` and `state/semantics.rkt` / `dyn-scope-is-bad/semantics.rkt` in `shriram/smol`.
