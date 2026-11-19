# Spatial Aggregate Field Calculi and Chemical Reaction Network Compilers

## Summary

Spatial aggregate programming (**Field Calculus**) and molecular programming (**Chemical Reaction Networks / DNA Strand Displacement**) represent two rigorous non-von-Neumann compilation paradigms that eliminate explicit per-node message routing and random-access memory addresses in favor of global **space-time fields** and **well-mixed molecular concentration dynamics**. In Higher-Order Field Calculus (Audrito, Viroli, Damiani, Pianini, Beal; implemented in `ScaFi`, `FCPP`, and `Protelis`), a single global expression over `rep` (time evolution), `nbr` (neighborhood observation), `branch` (spatial domain splitting), and higher-order function values compiles into local asynchronous device rounds whose exported **value-trees** enforce **domain alignment**: a device exchanges `nbr` values exclusively with neighbors whose dynamic call-stack path matches its own. Restricting programs to the self-stabilizing calculus fragment (`G` gradient-cast, `C` converge-cast, `T` time-decay) guarantees eventual convergence from arbitrary transient corruption and density-independent continuous-space limits, though naive Bellman–Ford gradients suffer linear count-to-infinity rising-value drift upon source failure.

In parallel, Chemical Reaction Network (CRN) compilers translate formal computation into addressless soups of reacting molecular species governed by either **deterministic mass-action ODEs** (continuous concentration limit) or **stochastic continuous-time Markov chains** (discrete molecule counts, Gillespie SSA). While rate-independent deterministic CRNs compute strictly **semilinear functions** (Chen, Doty, Soloveichik 2013/2014), finite stochastic CRNs are **Turing-universal with arbitrarily small error** (Soloveichik et al. 2008), and rate-dependent ODE languages like **`CRN++`** (Vasić, Soloveichik, Khurshid 2018/2020) compile sequential imperative loops, conditionals, and nonlinear arithmetic (`Mul`, `Dvd`, `Sqr`) by coupling mass-action steady-state macros to a cyclic $3p$-species rock-paper-scissors chemical oscillator and Cardelli's Approximate Majority (`AM`) comparator. Executing the exact `CRN++` ODEs independently reproduces its hardcoded phase-sampling schedule (`firstTick ≈ 18.13`, `tickInterval ≈ 36.10`), reveals an **unbounded helper-species accumulation hazard** in `Sub(a, b, c)` whenever $a < b$ (due to an omitted unary decay rule in `primitives.m`), and quantifies stochastic `AM` misclassification rising to `27.6%` at $N = 10$ molecules. Lowering abstract CRNs to physical DNA relies on **DNA Strand Displacement (DSD)** compilers (`Soloveichik 2010`, `Nuskell`) paired with Tarjan-SCC fast/slow reaction condensation (`Peppercorn`) and formal **CRN bisimulation / pathway-decomposition equivalence** verification (`nuskell/crnverifier.py`).

## Applicability

This report examines primary source implementations, formal calculi, and executable ODE/stochastic/network probes across two complementary paradigms:

1. **Spatial Aggregate Programming & Field Calculus**:
   - `ScaFi` (`scafi/scafi` @ `df8b4068d37a8fd14cc990cec090492882777bc2`): Scala internal DSL, `Constructs`, `RoundVM`, `Slot`/`Path` alignment (`Language.scala`, `Semantics.scala`, `RichLanguage.scala`).
   - `FCPP` (`fcpp/fcpp` @ `9e78292c4b555e12d060c10b5b107a8e9027a6cc`): C++ field-calculus runtime and reversible rolling hash stack traces (`src/lib/internal/trace.hpp`).
   - `Protelis` (`Protelis/Protelis` @ `f9004127313b0bf4a03cabfd139895fa4babfc80`): JVM external aggregate language.
   - Foundational formalizations: Beal, Pianini, and Viroli (2015), Viroli et al. (2018 TOMACS), Audrito et al. (2019 ACM TOCL), and Viroli et al. (2019 JLAMP).
2. **Chemical Reaction Network & DNA Strand Displacement Compilers**:
   - `CRN++` (`marko-vasic/crnPlusPlus` @ `a0c4f83a716add8b58355698465ac2c4fc59acc8`): imperative-to-CRN Mathematica compiler (`packages/primitives.m`, `packages/utils.m`) and Vasić, Soloveichik, and Khurshid (2018/2020).
   - `Nuskell` (`DNA-and-Natural-Algorithms-Group/nuskell` @ `73077a232da40de47fc61c48014c5cfd39f0e8f5`): CRN-to-DSD translation schemes (`nuskell/dsdcompiler/schemes/literature/soloveichik2010.ts`) and formal CRN equivalence verifier (`nuskell/crnverifier.py`), plus Badelt et al. (2017).
   - `Peppercorn` (`DNA-and-Natural-Algorithms-Group/peppercornenumerator` @ `488537edb75b4a6f3e911bb24d9f040e4e2483c9`): domain-level non-pseudoknotted DSD enumerator and Tarjan-SCC fast/slow condensation (`peppercornenumerator/condense.py`), plus Badelt et al. (2020).
   - Foundational CRN/DSD theory: Soloveichik, Cook, Winfree, and Bruck (2008), Soloveichik, Seelig, and Winfree (2010), Lakin et al. (2011), and Chen, Doty, and Soloveichik (2013/2014).

Source-level claims apply strictly to the pinned commit SHAs; mathematical theorems (semilinearity of rate-independent deterministic CRNs, stochastic CRN Turing universality, domain alignment semantics, and self-stabilizing combinator closure) hold for the abstract calculi defined in the cited peer-reviewed papers. Spatial reaction-diffusion PDEs, pseudoknotted DNA folding, and wet-lab sequence-level thermodynamics are explicitly bounded under **Boundaries**.

## Findings

### 1. Higher-Order Field Calculus: Space-Time Fields and Domain Alignment

*Basis: normative literature (Audrito et al. ACM TOCL 2019; Viroli et al. JLAMP 2019) + source (`scafi@df8b4068d3`, `fcpp@9e78292c4b`) + execution*

Rather than writing per-device `send`/`recv` handlers, **Aggregate Programming** models a distributed network of asynchronous, mobile devices as a continuous-like computational substrate whose first-class semantic object is a **computational field** $\Phi: \mathbf{E} \to V$ mapping space-time firing events $\epsilon = (\delta, t) \in \mathbf{E}$ to local values $v \in V$. Each event $\epsilon$ observes a finite causal neighborhood of recent message exports from spatially proximate devices ($\epsilon' \rightsquigarrow \epsilon$) and emits one new **export** (a finite map from syntactic/dynamic call-stack paths to values) broadcast to neighbors.

#### 1.1 Minimal Core Constructs & Operational Alignment Semantics

*Basis: normative literature (Audrito et al. 2019, DOI `10.1145/3285956`) + source (`scafi/scafi@df8b4068d3:Language.scala, Semantics.scala, RichLanguage.scala`)*

Higher-Order Field Calculus reduces distributed coordination to four orthogonal primitives (plus local/neighbor sensors `sense`, `nbrvar`, `mid`):

1. **Time Evolution (`rep(init)(f)`)**: Maintains per-device state across firing rounds by evaluating `f(prev)`, where `prev` is the device's own prior-round value at the current call-stack path (or `init` on the first round / after domain re-entry).
2. **Neighborhood Observation (`nbr(e)`)**: Evaluates `e` locally and constructs a **neighboring field** mapping every *aligned* neighbor $\delta'$ to the value $\delta'$ exported at the **exact same dynamic call-stack path** during its most recent round. In `ScaFi` (`Language.scala:16-36`), neighboring fields are avoided as explicit Scala types by pairing `nbr` with universal-quantification folding `foldhood(init)(aggr)(expr)` (plus `share(init)(f)` combining `rep` and `nbr` in one path slot, `Semantics.scala:110-132`).
3. **Domain Splitting (`branch(cond)(th)(el)` vs. `mux(cond)(th)(el)`)**:
   - In `branch`, devices evaluating `cond == true` enter a strictly isolated computational sub-domain from devices evaluating `cond == false`. Inside `th`, `nbr` sees **only** neighbors that also entered `th`—preventing cross-region state contamination and allowing independent algorithms to run concurrently in disjoint spatial partitions.
   - In `mux`, **both** branches are evaluated strictly on every device under the **same** call-stack path and the boolean merely selects the returned local value; neighbors remain aligned across the condition boundary.
   - Direct inspection of `scafi/scafi@df8b4068d3:RichLanguage.scala:18-21` confirms the exact mechanical difference:
     ```scala
     def branch[A](cond: => Boolean)(th: => A)(el: => A): A =
       mux(cond)(() => aggregate{ th })(() => aggregate{ el })()
     def mux[A](cond: Boolean)(th: A)(el: A): A = if (cond) th else el
     ```
     Because `aggregate` wraps its thunk in `vm.nest(FunCall(vm.index, s"${pos.file}:${pos.line}:${pos.col}"))` (`Semantics.scala:150-157`), the `th` and `el` thunks receive **distinct `FunCall` path slots** keyed by source location!
4. **Higher-Order Function Alignment**: In Higher-Order Field Calculus (Audrito et al. TOCL 2019), functions/closures are first-class field values that can be passed through `nbr` and `rep` (enabling dynamic mobile code deployment across a swarm). Applying a dynamic function value `f(e)` pushes the **function's identity** (`funId`) onto the alignment path so two neighboring devices executing *different* closures at the same call site do not misalign their internal `nbr`/`rep` slots!

#### 1.2 Alignment Data Structures Across Production Runtimes (`ScaFi` vs. `FCPP` vs. `Protelis`)

*Basis: source (`scafi@df8b4068d3`, `fcpp@9e78292c4b`, `Protelis@f900412731`)*

| Runtime | Host / Target | Alignment Path Representation | Alignment Check Mechanism | Higher-Order / Dynamic Branch Handling | Engineering Trade-Off |
|---|---|---|---|---|---|
| **`ScaFi`** (`df8b4068d3`) | Scala / JVM & JS | Explicit immutable `Path` = `List[Slot]` where `Slot ::= Nbr(i) \| Rep(i) \| FunCall(i, id) \| FoldHood(i) \| Scope(key)` (`Semantics.scala:32-51`) | `RoundVMImpl::alignedNeighbours()` filters neighbor exports for `p._2.get(status.path).isDefined` (`Semantics.scala:273-283`); missing slots throw `OutOfDomainException` caught in `foldedEval` (`lines 243-252`) | `aggregate` tags `FunCall` with `file:line:col`; explicit `align(key)` pushes `Scope(key)` (`Semantics.scala:159-162`) | Exact collision-free alignment and clean Scala embedding; higher packet/memory overhead for deep call trees |
| **`FCPP`** (`9e78292c4b`) | C++14 / Embedded & HPC Swarms | Fixed-width integer rolling hash `trace_t` (`FCPP_TRACE` $\in \{16, 24, 32, 48, 64\}$ bits) using compile-time `__COUNTER__` (`#define ___ __COUNTER__`, `trace.hpp:12-71`) | Reversible multiplicative hash (`k_hash_factor`, `k_hash_inverse` mod $2^{\text{k\_hash\_len}}$) pushed/popped in $O(1)$ via RAII guards (`trace_call`, `trace_key`, `trace_cycle`) | "Delayed alignment" (`trace.hpp:90`): `align` inserts keys into the rolling hash only on branching/loops | Zero heap allocation and fixed 2–8 byte wire headers per slot; non-zero birthday hash collision probability at `FCPP_TRACE=16/24` |
| **`Protelis`** (`f900412731`) | External JVM DSL | Explicit `CodePath` tree managed by `ExecutionContext` | Export map lookup by `CodePath` per aligned neighbor | First-class closures aligned by function identifier in Protelis VM | Decoupled syntax with dedicated alignment parser; separate language toolchain vs. host-embedded DSL |

#### 1.3 Domain Alignment Failure vs. Proper Isolation & The Rising-Value Problem

*Basis: normative literature (Viroli et al. TOMACS 2018, DOI `10.1145/3177774`) + execution (`probe_field_calculus_crn.py`, Section 1)*

Our micro-probe simulates a 6-node linear network (`0 -- 1 -- 2 -- 3 -- 4 -- 5`) partitioned into Region A (`{0, 1, 2}`, source at node `0`) and Region B (`{3, 4, 5}`, no source):

- **Aligned `branch`**: Pushes distinct `FunCall("T")` vs `FunCall("F")` slots. Nodes `2` and `3` are physically adjacent but unaligned, producing `{0: 0.0, 1: 1.0, 2: 2.0, 3: inf, 4: inf, 5: inf}` — exact isolation of Region B.
- **Unaligned `mux`**: Shares one path slot across the partition boundary, leaking node `0`'s gradient into Region B: `{0: 0.0, 1: 1.0, 2: 2.0, 3: 3.0, 4: 4.0, 5: 5.0}`.
- **Domain Alignment Anomaly with Naive Host Conditionals**: In embedded DSLs (`ScaFi`, `FCPP`), writing a raw host `if (cond) nbr(a) else nbr(b)` without wrapping each branch in `branch` / `align` (or `FCPP` `trace_call`) can assign identical path indices to both `nbr` calls, causing devices in opposite branches to **silently cross-align** or raise spurious `OutOfDomainException`s when recursion depths differ!

Furthermore, Viroli et al. (2018 ACM TOMACS, DOI `10.1145/3177774`) proved that a **syntactic self-stabilizing fragment** of Field Calculus built from three universal combinators guarantees eventual convergence from arbitrary initial/corrupted state to a unique equilibrium (and continuous-space density independence as node density $\rho \to \infty$):
- **`G` (Gradient-cast)**: computes shortest-path distance from source(s) and propagates source values outward.
- **`C` (Converge-cast)**: accumulates values over a monotonic potential field toward sinks (requiring idempotent/commutative aggregation on DAGs or single-parent spanning trees for non-idempotent sums).
- **`T` (Time-decay)**: bounded monotonic state decay ensuring transient faults wash out in finite time.

However, **even self-stabilizing naive `G`-blocks suffer severe transient slowdowns**. In our micro-probe, deleting source `0` from the converged naive Bellman–Ford gradient `[0, 1, 2, 3, 4, 5]` causes adjacent nodes to mutually reinforce each other's stale distances, creeping upward by only $+1$ hop per round (**count-to-infinity / rising-value problem**):
- Round `1`: `[2.0, 1.0, 2.0, 3.0, 4.0, 5.0]`
- Round `5`: `[6.0, 5.0, 6.0, 5.0, 6.0, 5.0]`
- Round `12`: `[12.0, 13.0, 12.0, 13.0, 12.0, 13.0]`

Production aggregate libraries therefore replace naive Bellman–Ford with **CRF (Constraint and Restoring Force)**, **BIS (Bounded Information Speed)**, or **ULT (Adaptive Bellman–Ford)** gradient algorithms that track temporal derivatives/timestamps to flush stale values at $O(\text{diameter})$ wave speed instead of $O(\text{diameter} \cdot V_{\max})$.

---

### 2. Chemical Reaction Networks: Deterministic ODE vs. Stochastic Computability Boundaries

*Basis: normative literature (Soloveichik et al. 2008; Chen, Doty, Soloveichik 2013/2014; Soloveichik, Seelig, Winfree 2010)*

A **Chemical Reaction Network (CRN)** is a pair $(\Lambda, \mathcal{R})$ of finite molecular species $\Lambda$ and irreversible reactions $r: \sum_{i} a_{r,i} X_i \xrightarrow{k_r} \sum_i b_{r,i} X_i$ with rate constants $k_r > 0$ (reversible reactions decompose into two irreversible reactions). CRNs admit two fundamentally distinct execution semantics:

1. **Deterministic Mass-Action ODEs (Macroscopic High-Copy Limit)**: Real-valued continuous concentrations $x_j(t) = [X_j](t) \in \mathbb{R}_{\ge 0}$ evolve deterministically via:
   $$\frac{dx_j}{dt} = \sum_{r \in \mathcal{R}} k_r (b_{r,j} - a_{r,j}) \prod_{i} x_i^{a_{r,i}}$$
2. **Stochastic CTMC / Gillespie SSA (Microscopic Discrete Limit)**: Non-negative integer molecule counts $\mathbf{c} \in \mathbb{N}^{|\Lambda|}$ jump stochastically with reaction propensities $\alpha_r(\mathbf{c}) = k_r V^{1 - \sum_i a_{r,i}} \prod_i \binom{c_i}{a_{r,i}}$ (volume $V$).

Three foundational computability theorems strictly bound what a CRN compiler can and cannot guarantee:

| Computational Regime | Exact Expressive Power Theorem | Source & DOI | Key Algorithmic Consequence |
|---|---|---|---|
| **Rate-Independent Deterministic CRN** (output invariant to all reaction orders & rates) | Computes $f: \mathbb{N}^k \to \mathbb{N}$ stably **if and only if** the graph of $f$ is **semilinear** (finite union of linear sets / Presburger-definable piecewise linear functions) | Chen, Doty, Soloveichik (2013/2014, DOI `10.1007/s11047-013-9393-6`) | Addition, subtraction, `min`/`max`, constant multiplication are rate-independent; **general multiplication $x \cdot y$, division $x/y$, and $\sqrt{x}$ are impossible** without rate dependence or stochastic error! |
| **Finite Stochastic CRN** (discrete counts, arbitrary error tolerance $\epsilon > 0$) | **Turing-universal** (computes any Turing-computable function with probability $\ge 1 - \epsilon$ for any $\epsilon > 0$) | Soloveichik, Cook, Winfree, Bruck (2008, DOI `10.1007/s11047-008-9067-y`) | Zero-testing a register species ($c_i = 0$?) cannot be done error-free in finite time by mass-action encounters; universality relies on slow-reaction exponential timing delays (`O(1/epsilon)` slowdown). |
| **Rate-Dependent Mass-Action ODE CRN + DNA Strand Displacement** | **Universal kinetic substrate**: any polynomial mass-action ODE CRN can be approximated uniformly on bounded time intervals $[0, T]$ by bimolecular DNA strand displacement gates | Soloveichik, Seelig, Winfree (2010 PNAS, DOI `10.1073/pnas.0909380107`) | Enables compiling arbitrary rate-dependent ODE languages (`CRN++`) down to physical DNA oligomers with error $O(1/C_{\max})$ as auxiliary fuel concentration $C_{\max} \to \infty$. |

---

### 3. `CRN++`: Imperative-to-Mass-Action Compilation, Oscillator Semantics, and Failure Modes

*Basis: source (`marko-vasic/crnPlusPlus@a0c4f83a71:packages/primitives.m, packages/utils.m`) + literature (Vasić, Soloveichik, Khurshid 2018/2020, DOI `10.1007/s11047-019-09775-1`) + execution*

Because chemical reactions fire concurrently across the entire well-mixed volume with no program counter, compiling imperative sequential programs (`step`, `ld`, `add`, `sub`, `mul`, `div`, `sqrt`, `cmp`, `ifGT`/`ifEQ`/`ifLT`) into deterministic mass-action CRNs requires synthesizing two compiler abstractions: **(1) a non-overlapping multi-phase chemical clock oscillator** and **(2) convergent steady-state arithmetic and comparison modules**.

#### 3.1 Exact Chemical Oscillator & Phase-Catalyst Compilation (`utils.m:85-138`)

Direct source inspection of `marko-vasic/crnPlusPlus@a0c4f83a71:packages/utils.m` shows how `CRN++` sequences $P$ sequential program steps:
- **`MakeOscillatorSpecies[phases, conc=1, speed=1]` (`utils.m:85-95`)**: Allocates $3P$ oscillator species $x_1, \dots, x_{3P}$ with initial concentrations $x_1(0) = x_2(0) = 1.0$ and $x_3(0) = \dots = x_{3P}(0) = 10^{-10}$, wired into a cyclic rock-paper-scissors autocatalytic ring:
  $$x_i + x_{i+1} \xrightarrow{\text{speed}} 2 x_{i+1} \quad (1 \le i < 3P), \qquad x_{3P} + x_1 \xrightarrow{\text{speed}} 2 x_1$$
  Because consecutive peaks are separated by 3 species in the ring (`GetOscillatorSpeciesName[phase] = x[3*phase]`, `utils.m:97-100`), the active catalysts $x_3, x_6, \dots, x_{3P}$ maintain mutually exclusive pulses (when $x_{3k}$ peaks at `2.0`, $x_{3(k\pm 1)}$ sits near $10^{-10}$).
- **`PhasifyRsys` (`utils.m:109-138`)**: Rewrites every reaction `rs -> ps` belonging to sequential step $k$ into a catalyzed reaction `x[3k] + rs -> x[3k] + ps`, gating execution strictly to phase $k$'s pulse window.

#### 3.2 Exact Compiled Arithmetic & Conditional Reactions (`primitives.m:141-301`)

| `CRN++` Macro | Source Location (`primitives.m`) | Compiled Mass-Action Reactions ($k = 1$ unless noted) | Mass-Action ODE Equilibrium | Critical Semantic / Numerical Caveat |
|---|---|---|---|---|
| `Add[a, b, c]` | `lines 170-180` | $a \to a + c$, $b \to b + c$, $c \to \emptyset$ | $\dot{c} = x_\phi(a + b - c) \implies c^* = a + b$ | Requires $c \notin \{a, b\}$; overwrites any prior $c(0)$ exponentially fast |
| `Mul[a, b, c]` | `lines 141-150` | $a + b \to a + b + c$, $c \to \emptyset$ | $\dot{c} = x_\phi(ab - c) \implies c^* = ab$ | Rate-dependent (`k_prod / k_decay = 1`); sensitive to kinetic rate mismatch |
| `Dvd[a, b, c]` | `lines 156-163` | $a \to a + c$, $b + c \to b$ | $\dot{c} = x_\phi(a - bc) \implies c^* = a / b$ | Slow convergence when $b$ is small; diverges if $b = 0$ |
| `Sub[a, b, c]` | `lines 187-198` | $a \to a + c$, $b \to b + h$, $c \to \emptyset$, $c + h \to \emptyset$ | $\dot{c} = x_\phi(a - c - ch)$, $\dot{h} = x_\phi(b - ch) \implies c^* = \max(0, a - b)$ | **No unary decay on helper $h$!** When $a < b$, $h$ grows unboundedly ($\dot{h} \to x_\phi(b - a) > 0$) |
| `Sqr[a, b]` | `lines 205-212` | $a \to a + b$ ($k=2$), $b + b \to \emptyset$ ($k=1$) | $\dot{b} = x_\phi(2a - 2b^2) \implies b^* = \sqrt{a}$ | Note: upstream comment at `line 201` erroneously repeats `Sub`'s docstring |
| `AM[x, y]` | `lines 215-226` | $x + y \to y + b$, $b + y \to 2y$, $y + x \to x + b$, $b + x \to 2x$ | Winner-take-all bifurcation to $(x+y, 0)$ or $(0, x+y)$ | Cardelli Approximate Majority; stochastic error rises sharply at low copy count $N$ |
| `NormalizeToFlags[x, y]` + `If{GT,LT,EQ,GE,LE}` | `lines 228-301` | Offsets $x, y$ by `cmpOffset = 0.5` into 4 flag species (`xgty`, `xlty`, `ygtx`, `yltx`, init `0.5`), then runs `FlagsAM[]`; guards inject `xgty+yltx` (`IfGT`), `xgty+ygtx` (`IfEQ`), etc. | Clean separation of $>$, $=$, $<$ for integer-spaced values ($\|x - y\| \ge 1$) | Fails to distinguish continuous values with $0 < \|x - y\| < 0.5$ (`cmpOffset`) |

#### 3.3 Executable Verification of `CRN++` Oscillator Drift, `Sub` Helper Runaway, and Stochastic Extinction

*Basis: execution (`probe_field_calculus_crn.py`, Sections 2–3)*

Integrating the exact 2-phase (6-species) `CRN++` ODE system via RK4 (`dt = 0.005`, `tmax = 120.0`) directly validates and stress-tests the compiler's numerical guarantees:

1. **Exact Reproduction of Hardcoded Phase Sampling Times**: Our RK4 integration measured the first `x3` peak at **`t = 18.1300`** (`x3_peak = 2.0000`) and the phase-to-phase delta (`x6` peak at `54.2300` minus `x3` peak at `18.1300`) as **`36.1000`**, matching `primitives.m:309–310`'s hardcoded `firstTick = 18.135824374899833` and `tickInterval = 36.098357644` to `< 0.03%`! On well-conditioned positive inputs, ODE approximation error is tiny:
   - Peak 1 (`t = 18.130`): `Add(3, 5) = 7.99994` (`|err| = 6e-5`); Peak 2 (`t = 90.155`): `8.00000`.
   - Second clock tick (`x6` peak, `t = 54.230`): `Mul(c, 2) = 15.99992` (`|err| = 8e-5`), `Sub(c, 2) = 5.99994` (`|err| = 6e-5`).
2. **Unbounded Helper Accumulation in `Sub(2, 5, d)`**: On the exact same phase-2 pulse (`t = 54.230`), `Sub(2, 5)` evaluates to `0.05068` (a `5%` residual tail error above true `0.0`) while the un-decayed `helper` species accumulates to **`38.543`** in a single clock tick! Because `primitives.m:187–198` contains no `helper -> trash` reaction, iterating a loop containing `Sub(a, b, c)` in the $a < b$ branch causes unbounded monotonic accumulation of `helper` molecules (which in physical DSD implementations permanently depletes finite fuel gates).
3. **Stochastic Low-Copy-Number Breakdown (`AM` Gillespie SSA, 500 trials, seed 42)**: Simulating `primitives.m:215–226`'s exact `AM` reactions on a `60%/40%` initial split ($X_0 = 0.6 N$, $Y_0 = 0.4 N$):

| Total Molecule Count $N$ | Initial $(X_0, Y_0)$ | Empirical $P(\text{converge to } X)$ | Misclassification Error Rate |
|---:|---|---:|---:|
| `10` | `(6, 4)` | `0.724` | **`27.6%`** |
| `20` | `(12, 8)` | `0.810` | **`19.0%`** |
| `40` | `(24, 16)` | `0.906` | **`9.4%`** |
| `100` | `(60, 40)` | `0.976` | **`2.4%`** |
| `200` | `(120, 80)` | `0.996` | **`0.4%`** |

Because `CRN++` relies on `AM` inside every `cmp` / `if*` branch, lowering a `CRN++` program into low-copy-number cellular or microfluidic droplet compartments ($N < 50$ copies per flag species) induces catastrophic branching corruption even when the deterministic ODE simulation is accurate to $10^{-5}$.

---

### 4. DNA Strand Displacement Compilation, Condensation, and Formal CRN Verification

*Basis: source (`nuskell@73077a232d`, `peppercornenumerator@488537edb7`) + normative literature (Soloveichik 2010; Lakin 2011; Badelt 2017, 2020)*

Compiling a formal CRN (such as `CRN++` output) into physical nucleic acid molecules requires lowering abstract species and $n$-ary reactions into bimolecular **toehold-mediated DNA strand displacement (DSD)** gates and verifying that the resulting detailed reaction network exhibits no unintended crosstalk, spurious polymers, or missing pathways.

#### 4.1 `Nuskell` & `Soloveichik 2010` Translation Architecture

Direct inspection of `DNA-and-Natural-Algorithms-Group/nuskell@73077a232d:nuskell/dsdcompiler/schemes/literature/soloveichik2010.ts` (`lines 17–94`) reveals the exact domain-level compiler lowering of Soloveichik, Seelig, and Winfree (2010 PNAS, DOI `10.1073/pnas.0909380107`):

- **Formal Signal Strands (`lines 17–22`)**: Every formal species $S$ is compiled to a single-stranded 3-domain DNA oligomer `"? a b c"` (`a = short` toehold, `b = long` branch-migration domain, `c = short` toehold; `?` wildcard history domain).
- **Two-Stage Reaction Module (`maingate`, `lines 56–90`)**: Each irreversible formal reaction $X_1 + \dots + X_m \to Y_1 + \dots + Y_n$ compiles to:
  1. A multi-stranded input-consuming **main gate `L_i`** that reversibly binds inputs $X_1, \dots, X_{m-1}$ (via `inputmac` reversible backward fuel strands `bi`) and irreversibly locks when $X_m$ displaces an intermediate flux strand;
  2. A **translator complex `T_i`** (`gmac`) triggered by the displaced flux strand to release product signal strands $Y_1, \dots, Y_n$;
  3. Auxiliary complexes `L_i`, `T_i`, and `bi` supplied in formal excess (`infty(l) + infty(t) + sum(map(infty, b))`) so their concentrations remain approximately constant ($C_{\max}$) over the computation horizon.
- **Scheme Library**: `nuskell/dsdcompiler/schemes/literature/` hosts 11 parameterized translation schemes (`soloveichik2010.ts`, `cardelli2011_FJ.ts`, `cardelli2011_NM.ts`, `cardelli2013_2D*.ts`, `chen2013_2D_JF.ts`, `lakin2012_3D.ts`, `lakin2016_2D_3I.ts`, `qian2011_3D.ts`, `srinivas2015.ts`) trading strand complexity (2-domain vs. 3-domain, cooperative vs. sequential gates) against leak rates and reversible intermediate overhead.

#### 4.2 `Peppercorn` Reaction Enumeration & Tarjan-SCC Condensation

Because DNA complexes can interact in combinatorially many unforeseen ways (unintended toehold binding, branch migration, spontaneous dissociation), `Peppercorn` (`DNA-and-Natural-Algorithms-Group/peppercornenumerator@488537edb7`; Badelt et al. 2020, DOI `10.1098/rsif.2019.0866`) exhaustively enumerates all domain-level non-pseudoknotted secondary-structure reactions and then reduces the resulting detailed CRN to a macroscopic **condensed CRN** (`peppercornenumerator/condense.py:22–100`):

1. **Fast vs. Slow Separation (`condense.py:69–70`)**: Classifies unimolecular (`arity[0] == 1`) reactions with rate $k \ge \max(k_{\text{slow}}, k_{\text{fast}})$ as **fast** (internal branch migration / rapid unbinding) and bimolecular encounters as **slow**.
2. **Tarjan SCC Macrostate Extraction (`condense.py:31–36, 77–100`)**: Runs Tarjan's strongly connected components (`tarjans`) on fast 1-to-1 reaction edges. An SCC with **zero outgoing fast reactions** (`len(out_rxns) == 0`) forms a **resting macrostate** (`PepperMacrostate`); transient SCCs decay instantaneously (in the fast-limit timescale separation) into probability distributions over reachable resting macrostates computed from internal CTMC stationary distributions (`get_stationary_distribution`).

#### 4.3 Formal CRN Equivalence Verification (`nuskell/crnverifier.py`)

Once `Peppercorn` condenses the enumerated DNA implementation into an implementation CRN (`icrn`), `Nuskell` (`nuskell/crnverifier.py:15–118`) verifies semantic equivalence against the source formal CRN (`fcrn`) using two complementary formal theories (Badelt et al. 2017, DOI `10.1007/978-3-319-66799-7_15`):
- **CRN Bisimulation (`crn_bisimulation_test`, `modular_crn_bisimulation_test`)**: Finds an interpretation mapping implementation species to multisets of formal species such that every implementation reaction either simulates a formal reaction or is a silent (`\tau`) step, and every formal reaction is permissively enabled (`graphsearch`, `loopsearch`, or `bruteforce` permissive checks, `crnverifier.py:59–70`). Preserves both stochastic CTMC trajectories and deterministic reachability.
- **Pathway Decomposition Equivalence (`pathway_decomposition_eq`, `crnverifier.py:71–73`)**: Checks equivalence via elementary formal reaction pathways (handling non-trivial multi-step intermediate couplings), complemented by hybrid checkers (`compositional_hybrid_test`, `integrated_hybrid_test`).

---

### 5. Cross-Paradigm Synthesis: Spatial Field Calculi vs. Molecular CRN Compilers

*Basis: derived from Sections 1–4*

| Architectural Dimension | Spatial Aggregate Field Calculus (`ScaFi`, `FCPP`, `Protelis`) | Molecular CRN / DSD Compilers (`CRN++`, `Nuskell`, `Peppercorn`) |
|---|---|---|
| **Primary Data Abstraction** | Space-time field $\Phi: \mathbf{E} \to V$ over causal device firing events | Concentration vector $\mathbf{x}(t) \in \mathbb{R}_{\ge 0}^{|\Lambda|}$ (ODE) or multiset $\mathbf{c} \in \mathbb{N}^{|\Lambda|}$ (CTMC) |
| **Addressing / Identity** | Device IDs (`mid`) + dynamic call-stack `Path`/`trace_t` alignment slots | **Addressless** well-mixed species names; variable identity = distinct DNA domain sequence |
| **Control Flow & Sequencing** | Synchronous-illusion `branch` domain splitting + asynchronous local rounds | $3P$-species autocatalytic clock oscillator (`PhasifyRsys`) + `AM` boolean catalyst flags |
| **Core Soundness Property** | **Domain alignment** (type/path safety) + **self-stabilization** (`G`/`C`/`T` closure) | **Semilinearity / ODE convergence** + **CRN bisimulation / pathway equivalence** |
| **Canonical Failure Modes** | Unaligned host `if`/`mux` leakage; Bellman–Ford rising-value count-to-infinity; rolling hash collision (`FCPP_TRACE=16`) | Unbounded `Sub` helper accumulation ($a < b$); phase-tail overlap drift; low-copy stochastic `AM` misclassification; DSD crosstalk/polymerization |
| **Verification / Analysis Tooling** | Static field-type checkers, self-stabilization syntactic fragments, `Alchemist` discrete-event simulation | `Peppercorn` Tarjan-SCC condensation + `Nuskell` `crnverifier` bisimulation + RK4 ODE / Gillespie SSA simulation |

## Boundaries

- **Continuous Spatial Reaction-Diffusion PDEs & Non-Well-Mixed CRNs (`not examined`)**: All CRN/DSD results in this report assume a **well-mixed** homogeneous solution (zero spatial concentration gradients). Spatially heterogeneous reaction-diffusion systems ($\partial_t u = D \nabla^2 u + R(u)$), Turing-pattern compilers, and DNA origami localized surface-tethered strand displacement (where spatial geometry replaces well-mixed kinetics) were not examined.
- **Pseudoknotted Secondary Structures & Nucleotide Sequence Design (`unsupported` / `not examined`)**: `Peppercorn` (`Badelt et al. 2020`) explicitly restricts enumeration to **non-pseudoknotted** domain-level secondary structures (`unsupported` for arbitrary pseudoknots). Sequence-level thermodynamic design (NUPACK free-energy minimization, spurious partial-domain binding / leak reactions, salt/temperature kinetics) was not examined.
- **Byzantine / Adversarial Faults in Field Calculus (`known not to apply`)**: The self-stabilization proofs of Viroli et al. (2018 TOMACS) establish recovery from **transient state corruption** and dynamic topology/input changes assuming non-Byzantine devices obeying the compiled Field Calculus round semantics. Persistent Byzantine nodes injecting forged `nbr` exports break unauthenticated `G`/`C` convergence (`known not to apply` without cryptographic/Byzantine-resilient aggregation extensions).
- **Large-Scale Stochastic `CRN++` Oscillator Extinction (`unknown` exact threshold)**: While our micro-probe quantified stochastic `AM` failure down to $N=10$ molecules, the exact minimum copy-number threshold at which `CRN++`'s $3P$-species cyclic oscillator (`x[i] + x[i+1] -> 2 x[i+1]`) suffers irreversible finite-population species extinction (hitting $c_i = 0$ where autocatalysis cannot recover) as a function of $P$ and initial volume was not analytically bounded (`unknown`; expected to scale unfavorably with $P$ because peak-to-trough ratio spans $10^{10}$ in `utils.m:91`!).
- **Visual DSD Proprietary/Standalone Runtime (`not examined`)**: Lakin et al. (2011, DOI `10.1093/bioinformatics/btr543`) is cited for domain-level DSD context, while direct source verification focused on the open-source `Nuskell` and `Peppercorn` repositories.

## Evidence

### Primary Git Repository Evidence (Observed `2026-11-19`)

1. **`scafi/scafi` @ `df8b4068d37a8fd14cc990cec090492882777bc2`**
   - `core/shared/src/main/scala/it/unibo/scafi/core/Language.scala` (lines 13–38): `Constructs` trait (`nbr`, `rep`, `foldhood`, `aggregate`, `align`, `share`, `mid`, `sense`, `nbrvar`) and local-only Scala embedding note.
   - `core/shared/src/main/scala/it/unibo/scafi/core/Semantics.scala` (lines 32–62, 110–167, 237–364): `Slot` ADT (`Nbr`, `Rep`, `FunCall`, `FoldHood`, `Scope`), `Path`, `ConstructsSemantics`, `RoundVMImpl::foldedEval` (`OutOfDomainException` handling), and `alignedNeighbours()` path-presence filter.
   - `core/shared/src/main/scala/it/unibo/scafi/core/RichLanguage.scala` (lines 15–37): `branch` vs. `mux` definitions (`mux(cond)(() => aggregate{ th })(() => aggregate{ el })()`).
2. **`fcpp/fcpp` @ `9e78292c4b555e12d060c10b5b107a8e9027a6cc`**
   - `src/lib/internal/trace.hpp` (lines 11–90): `#define ___ __COUNTER__`, configurable `FCPP_TRACE` (16/24/32/48/64-bit) rolling modular hash parameters (`k_hash_len`, `k_hash_factor`, `k_hash_inverse`), and delayed alignment guards (`trace_call`, `trace_key`, `trace_cycle`).
3. **`Protelis/Protelis` @ `f9004127313b0bf4a03cabfd139895fa4babfc80`**
   - Pinned upstream HEAD revision for external JVM Field Calculus comparison.
4. **`marko-vasic/crnPlusPlus` @ `a0c4f83a716add8b58355698465ac2c4fc59acc8`**
   - `packages/primitives.m` (lines 11–87, 141–315): `ExpandRsys`, `Mul`, `Dvd`, `Add`, `Sub`, `Sqr`, `AM`, `InitializeFlagConcentrations` (`0.5`), `NormalizeToFlags`, `FlagsAM`, `If{GT,LT,EQ,GE,LE}`, and `GetTimeOfPhaseMaxima` (`firstTick = 18.135824374899833`, `tickInterval = 36.098357644`).
   - `packages/utils.m` (lines 85–138): `MakeOscillatorSpecies` ($3P$ species, `conc[{x[1],x[2]}, 1]`, `conc[x[3..3P], 10^-10]`, cyclic `x[i]+x[i+1] -> 2x[i+1]`), `GetOscillatorSpeciesName` (`x[3*phase]`), and `PhasifyRsys`.
5. **`DNA-and-Natural-Algorithms-Group/nuskell` @ `73077a232da40de47fc61c48014c5cfd39f0e8f5`**
   - `nuskell/dsdcompiler/schemes/literature/soloveichik2010.ts` (lines 17–94): 3-domain `formal(s) = "? a b c"`, `maingate` (`L_i`, `T_i`, `bi`), and 10 peer literature schemes in `schemes/literature/`.
   - `nuskell/crnverifier.py` (lines 15–118): `verify` and `verify_modules` wrappers over `crn_bisimulation_test` (`graphsearch`/`loopsearch`/`bruteforce`), `modular_crn_bisimulation_test`, `pathway_decomposition_eq`, `compositional_hybrid_test`, and `integrated_hybrid_test`.
6. **`DNA-and-Natural-Algorithms-Group/peppercornenumerator` @ `488537edb75b4a6f3e911bb24d9f040e4e2483c9`**
   - `peppercornenumerator/condense.py` (lines 22–100): `PepperCondensation`, `is_fast` threshold (`arity[0] == 1 and k >= max(k_slow, k_fast)`), Tarjan SCCs (`tarjans`), `PepperMacrostate` resting states, and `get_stationary_distribution`.

### Peer-Reviewed Literature (Crossref-Verified `2026-11-19`)

- J. Beal, D. Pianini, M. Viroli, *"Aggregate Programming for the Internet of Things"*, IEEE Computer 48(9), 2015, DOI `10.1109/mc.2015.261`.
- M. Viroli, G. Audrito, J. Beal, F. Damiani, D. Pianini, *"Engineering Resilient Collective Adaptive Systems by Self-Stabilisation"*, ACM TOMACS 28(2), 2018, DOI `10.1145/3177774`.
- G. Audrito, M. Viroli, F. Damiani, D. Pianini, J. Beal, *"A Higher-Order Calculus of Computational Fields"*, ACM TOCL 20(1), 2019, DOI `10.1145/3285956`.
- M. Viroli, J. Beal, F. Damiani, G. Audrito, R. Casadei, D. Pianini, *"From distributed coordination to field calculus and aggregate computing"*, JLAMP 109, 2019, DOI `10.1016/j.jlamp.2019.100486`.
- D. Soloveichik, M. Cook, E. Winfree, J. Bruck, *"Computation with finite stochastic chemical reaction networks"*, Natural Computing 7(4), 2008, DOI `10.1007/s11047-008-9067-y`.
- D. Soloveichik, G. Seelig, E. Winfree, *"DNA as a universal substrate for chemical kinetics"*, PNAS 107(12), 2010, DOI `10.1073/pnas.0909380107`.
- M. R. Lakin, S. Youssef, F. Polo, S. Emmott, A. Phillips, *"Visual DSD: a design and analysis tool for DNA strand displacement systems"*, Bioinformatics 27(22), 2011, DOI `10.1093/bioinformatics/btr543`.
- H.-L. Chen, D. Doty, D. Soloveichik, *"Deterministic function computation with chemical reaction networks"*, Natural Computing 13(4), 2013/2014, DOI `10.1007/s11047-013-9393-6`.
- S. Badelt, S. W. Shin, R. F. Johnson, Q. Dong, C. Thachuk, E. Winfree, *"A General-Purpose CRN-to-DSD Compiler with Formal Verification, Optimization, and Simulation Capabilities"*, DNA 23 (LNCS), 2017, DOI `10.1007/978-3-319-66799-7_15`.
- M. Vasić, D. Soloveichik, S. Khurshid, *"CRN++: Molecular programming language"*, DNA 24 (LNCS, DOI `10.1007/978-3-030-00030-1_1`) and Natural Computing 19, 2020 (DOI `10.1007/s11047-019-09775-1`).
- S. Badelt, C. Grun, K. V. Sarma, B. Wolfe, S. W. Shin, E. Winfree, *"A domain-level DNA strand displacement reaction enumerator allowing arbitrary non-pseudoknotted secondary structures"*, Journal of the Royal Society Interface 17, 2020, DOI `10.1098/rsif.2019.0866`.

### Executable Micro-Probe (`Basis: execution`, `2026-11-19`, Python 3 Linux)

Executed exact Python simulation of (1) ScaFi-style path-keyed `branch` vs. `mux` gradient alignment and Bellman–Ford rising-value drift, (2) RK4 integration (`dt=0.005, tmax=120`) of `CRN++`'s 6-species oscillator (`utils.m`) + `Add`/`Mul`/`Sub` (`primitives.m`), and (3) Gillespie SSA (500 trials, seed 42) of Cardelli's `AM`:

```text
=== 1. Field Calculus Domain Alignment (branch vs mux) & G-block Rising-Value Problem ===
  Aligned `branch` (A={0,1,2} src=0; B={3,4,5} isolated, no src): {0: 0.0, 1: 1.0, 2: 2.0, 3: inf, 4: inf, 5: inf}
  Unaligned `mux` (shared path leaks src=0 across A/B boundary):      {0: 0.0, 1: 1.0, 2: 2.0, 3: 3.0, 4: 4.0, 5: 5.0}
  Naive Bellman-Ford after source loss (round  1): [2.0, 1.0, 2.0, 3.0, 4.0, 5.0] (count-to-infinity +1/round)
  Naive Bellman-Ford after source loss (round  5): [6.0, 5.0, 6.0, 5.0, 6.0, 5.0] (count-to-infinity +1/round)
  Naive Bellman-Ford after source loss (round 12): [12.0, 13.0, 12.0, 13.0, 12.0, 13.0] (count-to-infinity +1/round)

=== 2. CRN++ Exact Chemical Oscillator & Mass-Action ODE Convergence (utils.m & primitives.m) ===
  2-phase (6-species) oscillator x3 peaks (Add(3,5) [true=8.0]):
    t= 18.130, x3_peak=2.0000, c=7.99994 (abs_err=0.00006)
    t= 90.155, x3_peak=2.0000, c=8.00000 (abs_err=0.00000)
  2-phase (6-species) oscillator x6 peaks (Mul(c,2)=16, Sub(c,2)=6, Sub(2,5)=0):
    t= 54.230, x6_peak=2.0000, p=15.99992, d=5.99994, Sub(2,5)=0.05068, h_neg(unbounded helper)=38.543
  Measured first x3 peak=18.1300 (primitives.m firstTick=18.1358), phase delta=36.1000 (primitives.m tickInterval=36.0984), full period=72.0250

=== 3. Stochastic Gillespie SSA: Approximate Majority (AM) Error vs Molecule Count N ===
  Total N= 10 (X0=  6, Y0=  4, 60/40 split): P(converge to X)=0.724, misclassification=0.276
  Total N= 20 (X0= 12, Y0=  8, 60/40 split): P(converge to X)=0.810, misclassification=0.190
  Total N= 40 (X0= 24, Y0= 16, 60/40 split): P(converge to X)=0.906, misclassification=0.094
  Total N=100 (X0= 60, Y0= 40, 60/40 split): P(converge to X)=0.976, misclassification=0.024
  Total N=200 (X0=120, Y0= 80, 60/40 split): P(converge to X)=0.996, misclassification=0.004
```

## Revalidation

1. **Diff Upstream Semantics & Compiler Primitives**:
   - Check `ScaFi`: diff `core/shared/src/main/scala/it/unibo/scafi/core/{Language,Semantics,RichLanguage}.scala` against `df8b4068d3` for changes to `Slot`, `branch`, or `alignedNeighbours`.
   - Check `FCPP`: diff `src/lib/internal/trace.hpp` against `9e78292c4b` for changes to `FCPP_TRACE` widths or delayed alignment.
   - Check `CRN++`: inspect `packages/primitives.m` (`Sub[a_, b_, c_]`, lines 187–198) against `a0c4f83a71` to check whether a `helper -> trash` decay reaction or alternative subtraction module was added.
   - Check `Nuskell` & `Peppercorn`: inspect `nuskell/crnverifier.py` (`73077a232d`) and `peppercornenumerator/condense.py` (`488537edb7`) for new equivalence algorithms or non-1-to-1 fast condensation rules.
2. **Re-run the Self-Contained `CRN++` Oscillator & `Sub` Helper Probe**:
   ```bash
   python3 - <<'PY'
   st = [1.0, 1.0, 1e-10, 1e-10, 1e-10, 1e-10, 0.0, 0.0, 0.0] # x1..x6, Add(3,5), Sub(2,5), helper
   dt = 0.005
   def f(s):
       x = s[:6]; c, dn, hn = s[6:]
       dx = [x[i]*(x[(i-1)%6]-x[(i+1)%6]) for i in range(6)]
       return dx + [x[2]*(8.0 - c), x[5]*(2.0 - dn - dn*hn), x[5]*(5.0 - dn*hn)]
   p3 = p6 = None; px3 = p2x3 = px6 = p2x6 = 0.0
   for step in range(int(70.0/dt)):
       t = step*dt
       k1 = f(st); k2 = f([st[i]+0.5*dt*k1[i] for i in range(9)])
       k3 = f([st[i]+0.5*dt*k2[i] for i in range(9)]); k4 = f([st[i]+dt*k3[i] for i in range(9)])
       st = [max(0.0, st[i]+(dt/6.0)*(k1[i]+2*k2[i]+2*k3[i]+k4[i])) for i in range(9)]
       if p3 is None and px3 > 0.5 and px3 > p2x3 and px3 > st[2]: p3 = (t-dt, st[6])
       if p6 is None and px6 > 0.5 and px6 > p2x6 and px6 > st[5]: p6 = (t-dt, st[7], st[8])
       p2x3, px3, p2x6, px6 = px3, st[2], px6, st[5]
   assert abs(p3[0] - 18.13) < 0.05 and abs(p3[1] - 8.0) < 1e-3
   assert abs((p6[0] - p3[0]) - 36.10) < 0.05 and p6[2] > 30.0
   print(f"OK: x3_peak={p3[0]:.3f} Add={p3[1]:.5f}, delta={p6[0]-p3[0]:.3f}, Sub(2,5)={p6[1]:.5f}, helper={p6[2]:.3f}")
   PY
   ```
   A passing probe verifies the ODE clock periodicity, `Add` steady-state accuracy, and `Sub(2,5)` helper accumulation; validating physical DNA sequence kinetics requires running `Nuskell` + `Peppercorn` + sequence-level thermodynamic simulation (`NUPACK`) on concrete DNA sequences.
