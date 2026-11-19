# Hybrid ODE Languages, VeriPhy, and Real-to-Float Accuracy Compilation

## Summary

Compiling programs that interact with continuous physical dynamics or specify real-valued numerical mathematics encounters a structural boundary that conventional discrete type systems and IEEE-754 compilers do not track: **exact real semantics ($\mathbb{R}$) cannot be executed directly, and discrete decisions over continuous quantities are inherently partial or multi-valued.** Across the examined languages, provers, and numerical compilers, five load-bearing engineering mechanisms emerge:

1. **Time-kind separation and causality typing (`Zélus`, `INRIA/zelus`)**: Zélus separates combinational, discrete-time (`Tdiscrete of bool`), continuous-time (`Tcont`), static (`Tstatic of bool`), and probabilistic (`Tproba`) computations at the type level and enforces an acyclic strict partial order over causality tags (`C | H |-cfree e : ct`). Stateful discrete operators (`pre`, `->`, `last`) are forbidden inside continuous flows unless activated by a zero-crossing or horizon event, preventing solver-step-dependent semantics. Because numerical ODE solvers reject and retry integration steps, any foreign function invoked from `Tcont` code must be pure and rollback-safe—an obligation absent from C/FFI ABIs.
2. **Event detection is mathematically partial and solver-dependent**: Sign-sampling zero-crossing detectors miss even-multiplicity crossings inside a single step and all tangential touches (`g(t) = (t - t_0)^2`), while idealized rigid-impact models admit Zeno executions with infinitely many events before a finite accumulation time $t_\infty$. In co-simulation (`FMI 3.0`), determinate rollback requires optional capability flags (`canGetAndSetFMUState`, `canHandleVariableCommunicationStepSize`, and `Clock` super-dense time synchronization); omitting rollback on any single FMU introduces step-order-dependent drift.
3. **Hybrid verification and sandboxed compilation (`KeYmaera X`, `ModelPlex`, `VeriPhy`)**: KeYmaera X keeps its dL prover kernel small via uniform substitution, but discharges real arithmetic via a hardcoded whitelist of untrusted external QE oracles (`MathematicaQETool`, `Z3QETool`, `BigDecimalQETool$` in `Provable.proveArithmetic`). **VeriPhy (PLDI 2018) does not verify the untrusted controller**: it compiles a ModelPlex-verified *runtime monitor sandbox* from dL into CakeML machine code using **32-bit signed-integer interval arithmetic** (`Isabelle-dL/Interval_Arithmetic.thy`, omitting `0x80000000` for two's-complement symmetry and using sentinel bounds `NEG_INF`/`POS_INF`) with **three-valued logic** (`True`, `False`, `Unknown -> Fallback`). Its TCB explicitly retains HOL4/Isabelle cores (~12K LOC), a hand-translated Isabelle-to-HOL4 bridge, a hand-written proof-term parser, external arithmetic oracle validity, and untrusted-controller memory isolation.
4. **Real-to-float accuracy compilation splits sharply between sound range+error analyzers (`Rosa`, `Daisy`, `FPTaylor`, `VCFloat2`, `NumFuzz`/`Bean`) and unsound empirical rewriters (`Herbie`)**: Sound analyzers treat finite precision as a refinement of a real-valued specification indexed by an explicit input-range precondition, combining interval/affine/Taylor/SMT bounds and (in Rosa/Daisy) checking cross-branch **path divergence** near discontinuous guards where a $5.55 \times 10^{-17}$ float error yields an $O(1)$ output jump. Herbie reduces sampled ULP error via e-graphs, Taylor series, and regime splitting but provides no worst-case soundness certificate. Conversely, value-unsafe compiler flags (`gcc -O3 -ffast-math`) destroy exactness invariants such as Kahan compensated summation (observed error exploding from `0.0` to `-500000.0` on GCC 15.2.0), while FMA contraction (`-mfma -ffp-contract=fast`) breaks algebraic cancellation (`a*a - a*a != 0`).
5. **Elementary functions and constructive reals**: IEEE 754-2019 Clause 9 recommends but does not require correct rounding for elementary functions (`sin`, `exp`, `pow`), causing cross-`libm` and scalar-vs-SIMD last-bit divergence; `RLibm-All` and `CORE-MATH` resolve the table-maker's dilemma for fixed formats via polynomial synthesis and worst-case testing/proofs. Exact constructive reals (Boehm, PLDI 2020) make evaluation error-bounded on demand, but total equality is undecidable (Richardson 1968) and pure dyadic comparison diverges on equal reals such as $\sqrt{2}\cdot\sqrt{2}$ vs. $2$, requiring a rational+symbolic front layer (`UnifiedReal`) to terminate on common algebraic identities.

## Applicability

This report synthesizes primary source inspections, formal specifications, peer-reviewed theorems, and local execution probes across nineteen pinned subjects representing five interacting layers of physical and numerical compilation:

- **Hybrid ODE languages, solver bindings, and co-simulation ABIs**: `INRIA/zelus` (`5f6e4903103e136f52cdcefc13a9bdcff0f53abd`), `inria-parkas/sundialsml` (`27ae63cf9e6e45e4b820232d99366751e30a6b9f`), and the `modelica/fmi-standard` FMI 3.0 specification (`fff9c88a58e61cf8d71f1992457288bb3399460c`). Findings characterize how synchronous dataflow languages integrate continuous ODE solvers and how FMU co-simulation interfaces govern rollback and super-dense time.
- **Differential dynamic logic (dL), runtime monitoring, and verified CPS sandboxes**: `LS-Lab/KeYmaeraX-release` (`2753f99b53cea5f946386998a39faded05ede677`), `LS-Lab/Isabelle-dL` (`97770ed9ca8d6a633c59d11d799247f44cc62dc2`), `LS-Lab/Coq-dL` (`af7e7dc5cc44f8a3e24b2a6a154bfff7858dfb2b`), `CakeML/cakeml` (`2874b664e10939a3ee462215b2e068c89c1f70eb`), and Bohrer et al.'s VeriPhy paper (`10.1145/3192366.3192406`, PLDI 2018). Findings map the exact proof-carrying pipeline from real-valued hybrid safety theorems to machine-code monitor sandboxes and enumerate its exact TCB.
- **Sound real-to-float error analyzers, verified checkers, and type-based error calculi**: `malyzajko/rosa` (`68e58b8c2f334ddde0f7647dc2d9c9ecc30309af`), `malyzajko/daisy` (`6a6f47abdd231d3009444e9e1b8ce9febc28c27e`), `soarlab/FPTaylor` (`b5a77cae348400f21f83512210d9f43c4bffb381`), `VeriNum/vcfloat` (`a203b287a84b0e3c9bec136823b5622ebfde6ad6`), `ak-2485/NumFuzz` (`80c54f35348c60b8a1e95f1881adda8d2e9c1dfb` and `bean` branch `e100727bf2441be948e110601b1f566e1fe5815b`), and `AbsInt/CompCert` (`2685140bf72c959446981fb99b5e44a8975021bc`).
- **Empirical accuracy rewriting and benchmarks**: `herbie-fp/herbie` (`4612b0d493cbb2013dc5afac5c099b7722166ec2`) and `FPBench/FPBench` (`090d81982edc0d2a597f4c15644253d4f266a6ef`).
- **Correctly rounded elementary libraries and constructive reals**: `rutgers-apl/rlibm-all` (`90431a000071e415abf0f403b6125c385551e346`), `Cactus-proj/core-math` (`74fcd1094a316164c94481f40f5c9658439bee63`), and Boehm's PLDI 2020 API (`10.1145/3385412.3386037`, Android `crcalc` `349dbd732e48cf93b11291291e056fc5a3829f31`).

**Scope relationships and exclusions**: The systems are analyzed comparatively as alternative mechanisms along the real-to-machine refinement boundary. Low-level IEEE-754 hardware ISA lowering, NaN payload propagation rules in Rust/LLVM, and SIMD associative-reduction certificates are outside this report's focus except where compiler flags (`-ffast-math`, `-ffp-contract=fast`) invalidate numerical accuracy invariants. All local execution probes were run on x86_64 Linux with Python 3.13 and `gcc (Debian 15.2.0-14) 15.2.0`; compiler optimization observations apply strictly to that compiler/target unless revalidated on other toolchains.

## Findings

### 1. Synchronous Hybrid ODE Languages: Zélus Kind Discipline, Causality Typing, and Solver Coupling

#### 1.1 Time Kinds and Internal State Classification in `INRIA/zelus`
Basis: source (`INRIA/zelus@5f6e4903103e136f52cdcefc13a9bdcff0f53abd`, `compiler/global/deftypes.ml:L39-L107`) + documentation (Bourke & Pouzet, HSCC 2013, `10.1145/2461328.2461348`)

Zélus conservatively extends a Lustre-like synchronous dataflow language with ordinary differential equations (`der x = e init e0`) and zero-crossing event detectors (`up(e)`). Rather than relying on simulator evaluation order to define meaning, the compiler statically classifies every arrow type `Tfun of kind * Zident.t option * typ * typ` with an explicit execution kind (`compiler/global/deftypes.ml:L66-L69`):

```ocaml
and kind =
  | Tstatic of bool     (* compile-time static argument *)
  | Tany                (* combinational / polymorphic over discrete & continuous *)
  | Tcont               (* continuous-time hybrid function (may contain ODEs / up) *)
  | Tdiscrete of bool   (* discrete-time node: true = stateful, false = stateless *)
  | Tproba              (* probabilistic synchronous node extension *)
```

Internal state variables are further segregated by `mkind` (`compiler/global/deftypes.ml:L100-L106`):
- `Cont`: continuous state variable carrying both position and derivative (`x`, `der x`).
- `Zero`: zero-crossing surface registered with the ODE solver's root-finding vector.
- `Horizon`: dynamically scheduled future wake-up instant.
- `Period`: periodic discrete event clock.
- `Encore`: cascade event triggering an additional super-dense discrete micro-step at the same continuous instant.
- `Major`: boolean guard indicating whether the runtime is in a discrete (major) step rather than a speculative continuous (minor) solver evaluation.

The type rule enforces that discrete stateful operators (`pre`, `fby`, `->`, and discrete state updates) are legal only inside `Tdiscrete` nodes or under an activation guard aligned to a `Zero`/`Horizon`/`Period` event—never directly inside a `Tcont` continuous flow. This eliminates the classic block-diagram bug of inserting a unit delay (`1/z`) inside a continuously integrated path, whose runtime value would otherwise depend on how many internal step rejections and Jacobian evaluations an adaptive solver performs.

#### 1.2 Causality Analysis as Strict Partial-Order Type Inference
Basis: source (`INRIA/zelus@5f6e4903103e136f52cdcefc13a9bdcff0f53abd`, `compiler/analysis/causality.ml:L17-L180`) + documentation (Bourke & Pouzet, HSCC 2014 / *NAHS* 2017)

Instantaneous algebraic loops (e.g., `x = y + 1 and y = x`) make synchronous step functions unschedulable and can hide high-index differential-algebraic equations. Zélus rejects them via a type-and-effect causality check of the form `C | H |-cfree e : ct` (`compiler/analysis/causality.ml:L17-L28`):
- Every leaf of a causality type `ct` is a causality tag (logical timestamp) `c` ordered by a strict partial order `<`.
- `c1 < c2` means expression `e1` must be computed strictly before `e2` within the same instant.
- `cfree` bounds all free variables of a block so that atomic function calls treat outputs as depending on all inputs unless given a finer polymorphic causality signature.
- State reads (`last x`, `pre x`) and continuous state positions `x` break instantaneous cycles because their values come from the previous instant or integrator state vector, whereas `der x` depends instantaneously on its right-hand side.
- When `Causal.less actual_tc expected_tc` detects a cycle, it raises `Causal.Clash(cycle)` and reports the minimal shrunk cyclic variable dependency (`compiler/analysis/causality.ml:L78-L131`). Records are treated atomically for causality (`compiler/analysis/causality.ml:L162-L166`), whereas tuples track per-component causality tags (`Etuplepat` -> `product`).

#### 1.3 Solver-Step Speculation, Zero-Crossing Undecidability, and Zeno Chattering
Basis: execution (Probe 1A under Evidence) + source (`INRIA/zelus`, `inria-parkas/sundialsml`) + documentation (Zhang et al., *IJRNC* 2001; Bourke, Inoue, Pouzet, EPTCS 285, 2018)

Compiling a hybrid model produces step callbacks (`step`, `derivatives`, `zero_crossings`, `reset`) driven by a numerical solver (such as SUNDIALS CVODE/IDA via `Sundials/ML`). Four structural hazards arise across this boundary:

1. **Speculative rollback across FFI**: Adaptive solvers (e.g., BDF/Adams-Moulton in CVODE) repeatedly evaluate `f(t, y)` at trial times, reject steps whose local error exceeds `(rtol, atol)`, contract step size `h`, and re-evaluate. Any foreign C/Rust function reachable from `Tcont` code is invoked speculatively and non-monotonically in time. Side effects (I/O, logging, actuator writes, stateful caches) corrupt semantics; standard C ABIs carry no "pure & rollback-safe" contract. In `Sundials/ML`, bridging OCaml and C additionally requires pinning C-owned `N_Vector` payloads against OCaml's moving garbage collector and marshaling exceptions across C-to-OCaml callback frames (`inria-parkas/sundialsml@27ae63cf9e`, `README.md`).
2. **Zeno executions**: An idealized bouncing ball ($h_0 = 1.0\,\text{m}$, $g = 9.81\,\text{m/s}^2$, restitution $e = 0.5$) exhibits infinitely many discrete impacts before the finite Zeno accumulation time:
   $$t_\infty = \sqrt{\frac{2h_0}{g}} \cdot \frac{1+e}{1-e} = \sqrt{\frac{2}{9.81}} \cdot 3 \approx 1.3545709230\,\text{s}.$$
   In Probe 1A (under Evidence), simulating with event-root refinement hits a 1000-bounce cutoff right at $t_\infty$ across all tested step sizes (`dt = 1e-2`: `stopped_t = 1.3545709230 s`, err `+1.332e-15`; `dt = 1e-3`: err `-5.440e-14`; `dt = 1e-4`: err `-2.598e-14`), freezing physical time progression at $v \to 0$. Simulink similarly caps consecutive zero-crossings (default 1000) and halts.
3. **Missed even-multiplicity and tangential crossings**: For a computable real guard $g(x(t))$, exact equality $g = 0$ is undecidable; only $g > 0$ and $g < 0$ are semi-decidable. Sign-sampling detectors check `sign(g(t_k)) != sign(g(t_{k+1}))`. In Probe 1A:
   - For $g_{\text{even}}(t) = (t - 0.5)^2 - 0.002^2$ (two transverse roots at $t = 0.498$ and $t = 0.502$ with slopes $\pm 0.004$), a step grid $t_0 = 0.450, h = 0.01$ brackets both crossings (`[(0.49, 0.5), (0.5, 0.51)]`), whereas shifting the grid phase by $0.005$ ($t_0 = 0.455, h = 0.01$) evaluates $g(0.495) > 0$ and $g(0.505) > 0$, **silently missing both crossings** (`[]`).
   - For a tangential touch $g_{\text{tang}}(t) = (t - 0.5)^2$ (root at $t = 0.5$, slope $0$), sign-change detection returns `[]` on every grid phase because $g$ never turns negative.
4. **Acausal DAEs and FMI 3.0 co-simulation rollback**: Acausal equation-based languages (Modelica) must compute causality globally via Pantelides index reduction and dummy derivatives; multi-mode DAEs can change differentiation index at mode switches. Across tool boundaries, **FMI 3.0** (`modelica/fmi-standard@fff9c88a58`, `docs/2_2_common_mechanisms.adoc:L575-L670`) introduces first-class `fmi3Clock` variables (`input Clock` and `triggered` `output Clock`) denoting super-dense time instants (`EventMode`) to synchronize events across FMUs. Crucially, however, FMU state save/restore (`fmi3GetFMUState` / `fmi3SetFMUState`) remains **optional**, gated on the capability flag `canGetAndSetFMUState="true"` (`docs/2_2_common_mechanisms.adoc:L575`, and serialization additionally gated on `canSerializeFMUState`, `L608`). If any FMU in a co-simulation loop lacks `canGetAndSetFMUState`, a rejected macro-step or mid-step event in another FMU cannot roll the composite system back to the exact event instant, breaking determinate composition (Broman et al., EMSOFT 2013).

#### 1.4 Comparative Semantics: Zélus vs. Simulink vs. Modelica/FMI 3.0
Basis: source (`INRIA/zelus`, `modelica/fmi-standard`) + documentation (Bourke & Pouzet HSCC 2013; MathWorks Simulink docs; Broman et al. EMSOFT 2013)

| Semantic / Compilation Dimension | Zélus (`INRIA/zelus@5f6e490310`) | Simulink / Stateflow | Modelica + FMI 3.0 (`fff9c88a58`) |
|---|---|---|---|
| **Unit delay inside continuous flow** | Statically rejected by kind checker (`Tdiscrete` ops illegal in `Tcont` without event activation) | Permitted; sample time inherited or solver-step-dependent unless explicitly rate-transitioned | Discrete `pre(x)` restricted to `when` clauses / clocked partitions (`Clock` variables in FMI 3.0) |
| **Instantaneous algebraic loops** | Statically rejected by strict partial-order causality typing (`compiler/analysis/causality.ml`) | Detected at simulation setup; solved iteratively via numeric algebraic-loop solver or rejected | Acausal by design; sorted via Tarjan SCC + Pantelides index reduction; cross-FMU loops require master iteration |
| **Tangential / even-count zero-crossings** | Sign-based `up(e)` passed to solver root-finder (SUNDIALS); tangential touches and intra-step double crossings can be missed | Sign-based adaptive zero-crossing detection; MathWorks documents 1000-consecutive limit and missed crossings under loose tolerances | Event indicators in FMI ME / CS EventMode; same sign-crossing limitation unless enclosed by validated integrator |
| **Rollback across FFI / components** | Continuous `Tcont` functions must be pure (unforced across OCaml/C FFI) | S-Functions may hold arbitrary C state; rollback only if S-Function implements state save | Explicit optional capability flag `canGetAndSetFMUState` in `modelDescription.xml` |

---

### 2. Differential Dynamic Logic, KeYmaera X, ModelPlex, and VeriPhy

#### 2.1 KeYmaera X Kernel Architecture and the Untrusted Arithmetic Oracle
Basis: source (`LS-Lab/KeYmaeraX-release@2753f99b53cea5f946386998a39faded05ede677`, `keymaerax-core/src/main/scala/org/keymaerax/core/{Proof.scala, QETool.scala}`) + documentation (Platzer, *JAR* 2017; Fulton et al., CADE 2015; Platzer & Tan, *JACM* 2020)

Differential dynamic logic ($\text{dL}$) specifies hybrid programs $\alpha$ (`x := θ`, `?H`, `x' = f(x) & Q`, `α ∪ β`, `α; β`, `α*`) with modal safety assertions $\phi \to [\alpha]\psi$. KeYmaera X minimizes its soundness-critical kernel (`Provable` in `Proof.scala:L188-L610`, ~1,700 LOC in the CADE 2015 kernel) by using Platzer's **uniform substitution calculus**: axioms are concrete formulas (`AxiomBase.loadAxioms`, `Proof.scala:L519-L537`) rather than syntactic axiom schemata, instantiated by one admissibility-checked substitution rule (`USubst`). ODE invariants are proved via differential invariants, differential cuts, and vectorial differential ghosts (`Provable.vectorialDG`, `Proof.scala:L626-L640`) without computing closed-form analytical ODE solutions.

However, source inspection of `Proof.scala:L514-L610` confirms the exact soundness boundary where the small kernel trusts external solvers:

```scala
private val trustedTools: immutable.List[String] =
  "org.keymaerax.tools.qe.MathematicaQETool" ::
  "org.keymaerax.tools.qe.Z3QETool" ::
  "org.keymaerax.tools.qe.BigDecimalQETool$" :: Nil

final def proveArithmetic(tool: QETool, f: Formula): Provable = {
  insist(trustedTools.contains(tool.getClass.getCanonicalName), ...)
  val equivalent = tool.quantifierElimination(f)
  oracle(Sequent(IndexedSeq(), IndexedSeq(Equiv(f, equivalent))), IndexedSeq())
}
```

Every real-arithmetic subgoal (first-order theory of real closed fields, decidable via Tarski/CAD with doubly exponential worst-case complexity, Davenport & Heintz 1988) is closed via `Provable.oracle(...)` (`Proof.scala:L609`, annotated `@note soundness-critical magic/trustme` at `L873`), trusting the class-name-whitelisted `QETool` (`MathematicaQETool`, `Z3QETool`, or `BigDecimalQETool$`) without kernel-checked Positivstellensatz or sum-of-squares certificates.

#### 2.2 ModelPlex: Runtime-Checked Contracts with Physical Reality
Basis: source (`LS-Lab/KeYmaeraX-release@2753f99b53`, `keymaerax-core/src/main/scala/org/keymaerax/btactics/ModelPlex.scala`) + documentation (Mitsch & Platzer, *FMSD* 2016; VeriPhy PLDI 2018 §3)

A dL theorem $\phi \to [(\text{ctrl}; \text{plant})^*]\psi$ establishes safety only for states obeying the mathematical model `ctrl` and `plant`. ModelPlex synthesizes, by proof inside dL, quantifier-free real-arithmetic monitor formulas over pre- and post-states $(\vec{x}, \vec{x}^+)$:
- **Controller monitor** $\text{ctrlMon}(\vec{x}, \vec{x}^+)$: checked *before* actuation to validate whether an arbitrary **untrusted controller**'s proposed decision $\vec{x}^+$ complies with the verified abstract model `ctrl`. If false or unknown, the sandbox overrides with a verified safe `fallback` action (e.g., braking/stopping).
- **Plant monitor** $\text{plantMon}(\vec{x}, \vec{x}^+)$: checked *after* physical evolution against newly sensed state to test whether nature obeyed the ODE/domain assumptions in `plant` (including control-period timing $\le \varepsilon$).

As VeriPhy (§1, §3) explicitly notes, runtime monitoring enforces a **contract with nature**: offline safety transfers to the physical run up through the current state *provided* the plant monitor holds; fallback safety "cannot be guaranteed when all of the physical assumptions are violated."

#### 2.3 VeriPhy End-to-End Pipeline, 32-Bit Integer Interval Semantics, and Trusted Computing Base
Basis: source (`LS-Lab/Isabelle-dL@97770ed9ca8d6a633c59d11d799247f44cc62dc2`, `Interval_Arithmetic.thy:L11-L95,L5007-L5039`, `Proof_Checker.thy:L5343-L5635`) + documentation (`VeriPhy`, PLDI 2018, `10.1145/3192366.3192406`, §1, §3–§5) + execution (Probe 1B under Evidence)

VeriPhy bridges verified dL models to executable machine code across a three-prover pipeline:
1. **KeYmaera X** proves $\phi \to [(\text{ctrl}; \text{plant})^*]\psi$, synthesizes the ModelPlex sandbox theorem $\phi \to [\text{sandbox}]\psi$ (VeriPhy Theorem 4), and exports an explicit proof term (~200,000 proof steps in the corridor robot case study).
2. **Isabelle/HOL (`LS-Lab/Isabelle-dL`)** mechanizes dL denotational semantics (`Denotational_Semantics.thy`), uniform substitution soundness (`USubst_Lemma.thy`), a proof-term checker (`Proof_Checker.thy`, VeriPhy Theorem 5: `arith_valid pt ∧ pteval pt = Some rule → sound(rule)`), and a computable **32-bit signed-integer interval arithmetic** semantics (`Interval_Arithmetic.thy`) proved sound against the real semantics (`theorem fixed_point_sound`, `Interval_Arithmetic.thy:L5007-L5036`; VeriPhy Theorems 7–8 and Corollary 9).
3. **HOL4 + CakeML** extracts the executable proof checker (rechecking ~200K steps in ~6.5 s vs. days inside Isabelle/HOL) and compiles the interval sandbox monitor to verified machine code via CakeML's verified compiler (`CakeML/cakeml`).

**Critical representation correction verified directly in `Interval_Arithmetic.thy:L11-L54`**: VeriPhy does **not** use IEEE-754 floating-point intervals. It represents each real state variable as a pair of 32-bit signed machine words (`type_synonym word = "32 Word.word"`, `wstate = "(ident + ident) => word"`), explicitly excluding `0x80000000` (`(* Note: 0x80000000 is never used. This way there's no awkward asymmetry ... *)`, `L25-L26`) so valid words lie in `[NEG_INF .. POS_INF]` (`-2147483647 .. +2147483647`), where `NEG_INF` represents $(-\infty, \text{NEG\_INF}]$ and `POS_INF` represents $[\text{POS\_INF}, +\infty)$ (`inductive repe`, `L27-L31`). Outward-rounded integer interval operators (`pu`, `pl`, `tu`, `tl`, `divu`, `divl`) saturate to `NEG_INF`/`POS_INF` on overflow.

Formula evaluation is **three-valued** ($\{\top, \bot, U\}$):
- For $\theta_1 < \theta_2$, evaluation returns $\top$ only if $\overline{\theta_1} < \underline{\theta_2}$, $\bot$ only if $\underline{\theta_1} \ge \overline{\theta_2}$, and **unknown ($U$)** whenever intervals overlap (VeriPhy Theorem 7).
- Because the sandbox executes the nondeterministic choice `(?ctrlMon ∪ fallback)`, **`Unknown` fails safely to `fallback`**.

In Probe 1B (under Evidence), evaluating VeriPhy's corridor braking guard $d \ge \varepsilon v_{\text{prop}}$ ($\text{req} = [500, 500]$) confirms:
- `d = [505, 515]` $\Rightarrow$ `True` (allows untrusted controller),
- `d = [498, 508]` $\Rightarrow$ `Unknown` (triggers safe `FALLBACK_STOP` even though real distances in $[500, 508]$ were safe),
- `d = [480, 490]` $\Rightarrow$ `False` (`FALLBACK_STOP`),
- Interval dependency blowup: for `x = [10, 12]`, `x - x` evaluates to `[-2, 2]`, so `x - x >= 0` evaluates to `Unknown` rather than `True`, demonstrating how repeated variables in monitor expressions can cause spurious fallback overrides.

**VeriPhy Trusted Computing Base (exact audit from VeriPhy PLDI 2018 §1 "Trusted Computing Base" & §4.1)**:

| TCB Component | What Is Trusted (Paper Wording / Source Anchor) | Mitigating Cross-Check / Residual Risk |
|---|---|---|
| **Isabelle/HOL & HOL4 kernels** | "The cores of HOL4 and Isabelle/HOL ($\approx$12K lines, well-tested) are sound." | Trust in Isabelle/HOL is partial for dL safety: requires simultaneous failure of both KeYmaera X and Isabelle/HOL kernels. |
| **Isabelle/HOL $\to$ HOL4 hand translation** | "Translations of definitions from Isabelle/HOL to HOL4 must be accurate. Some are nontrivial, e.g. we simulate Isabelle/HOL's typeclasses manually in HOL4." | Manual translation exists solely because Isabelle lacked verified machine-code extraction while HOL4 had CakeML (`§4.1`, p. 622). |
| **Proof-term parser** | "The hand-written proof term parser is correct." | Checker prints parsed proof conclusion for human cross-inspection. |
| **External real-arithmetic QE oracle** | "Arithmetic solving is sound." / Theorem 5 premise `arith_valid pt`: "This assumes all arithmetic goals in the proof are true." | Relies on Mathematica/Z3; proof-producing real QE left to future work (`§4.1`). |
| **Untrusted controller isolation** | "Untrusted controllers obey memory isolation with respect to the sandbox controller." | Same-address-space execution assumes no memory corruption of sandbox state. |
| **Sensor/actuator FFI & physical timing** | Sensing soundness ($\omega \in [[\omega_I]]$, Corollary 9) and unverified WCET (control period overrun caught only *ex post* by `plantMon`). | Physical assumption violations outside the model invalidate fallback safety guarantees. |

---

### 3. Sound Real-to-Float Compilation, Empirical Rewriting, and Verification Stacks

#### 3.1 Rosa and Daisy: Range + Error Refinement and Path Divergence
Basis: source (`malyzajko/daisy@6a6f47abdd231d3009444e9e1b8ce9febc28c27e`, `README.md`, `src/main/scala/daisy/tools/RoundoffEvaluators.scala:L26-L160`; `malyzajko/rosa@68e58b8c2f`) + documentation (Darulova & Kuncak, POPL 2014 / `arXiv:1309.2511`; Darulova et al., TACAS 2018; Becker et al., FMCAD 2018 / `arXiv:1707.02115`) + execution (Probe 1C under Evidence)

Rosa (POPL 2014) and its modular successor Daisy (TACAS 2018) treat finite-precision arithmetic as a **compilation refinement** of a real-valued program annotated with input ranges, optional initial input uncertainties, and a target absolute/relative error bound. In `Daisy` (`RoundoffEvaluators.scala:L26-L129`):
- **Composable range/error domains**: Daisy decouples real-range estimation (`Interval`, `AffineForm`, or `SMTRange` backed by Z3/dReal binary-search tightening over nonlinear real arithmetic) from roundoff error propagation (`uniformRoundoff_IA_AA`, `uniformRoundoff_AA_AA`, `uniformRoundoff_SMT_AA`, plus `FPTaylorPhase` and `IntervalSubdivision`).
- **Sterbenz cancellation awareness**: `RoundoffEvaluators.scala:L127-L129` directly checks `sterbenzTheoremApplies(x, y)` (`x.xhi <= 2 * y.xlo && y.xhi <= 2 * x.xlo`), setting the local subtraction roundoff term to zero when Sterbenz's Lemma guarantees exact subtraction.
- **Mixed-precision & rewriting**: Daisy supports `.scala`, `.c`, and `FPCore 2.0` inputs (`--treesitter`, `README.md:L75-L88`), mixed-precision type assignment (`MixedPrecisionOptimizationPhase.scala`), genetic/algebraic rewriting (`RewritingOptimizationPhase.scala`), and fixed-point code generation alongside IEEE floats.
- **Path divergence (discontinuous branches)**: When an ideal real execution and a finite-precision execution evaluate a branch guard $g(\vec{x}) < 0$ differently near zero (within the guard's error envelope $\delta_g$), the error is no longer bounded by rounding error along one path—it becomes the **gap between the two branch bodies** $|e_{\text{then}}(\vec{x}) - e_{\text{else}}(\tilde{\vec{x}})|$. Rosa (`arXiv:1309.2511`, §1.2) avoids requiring a separate continuity proof by directly encoding the cross-branch difference on the uncertainty band $|g(\vec{x})| \le \delta_g$ into SMT+range queries. Probe 1C illustrates the exact mechanism on $h(x) = \text{if } (0.1 + 0.2 - 0.3 \le 0) \text{ then } +1.0 \text{ else } -1.0$: exact arithmetic gives $0 \le 0 \Rightarrow +1.0$, whereas IEEE-754 `binary64` evaluates `0.1 + 0.2 - 0.3 = 5.551e-17 > 0` $\Rightarrow -1.0$, amplifying a $5.55 \times 10^{-17}$ roundoff into an absolute output error of **`2.0`**.
- **Interval vs. affine precision**: Probe 1C on $p(x) = x(1-x)$ over $x \in [0.4, 0.6]$ (exact range $[0.24, 0.25]$, width $0.01$) produces interval range $[0.16, 0.36]$ (width $0.20$, $20\times$ exact) versus standard affine arithmetic $[0.24, 0.26]$ (width $0.02$, $2\times$ exact) because affine noise symbols cancel the linear correlation between $x$ and $1-x$.
- **Verified certificate checking**: Becker et al. (FMCAD 2018, `arXiv:1707.02115`) decouple Daisy's untrusted Scala analyzer from soundness by emitting roundoff certificates re-checked independently in Coq and HOL4 (including via a CakeML-extracted verified binary).

#### 3.2 Herbie: Sample-Guided Catastrophic-Cancellation Rewriting (Useful and Unsound)
Basis: source (`herbie-fp/herbie@4612b0d493cbb2013dc5afac5c099b7722166ec2`, `src/core/mainloop.rkt:L39-L88`, `src/core/regimes.rkt`) + documentation (Panchekha et al., PLDI 2015; Sanchez-Stern et al., PLDI 2018; Damouche et al., NSV 2016) + execution (Probe 1C under Evidence)

Herbie (`src/core/mainloop.rkt:L39-L88`) automates accuracy repair for FPCore floating-point expressions through an iterative loop (`run-improve!`):
1. **Sampling & ground truth**: Samples input points (`train-pcontext`, `validation-pcontext`) and evaluates exact real ground truth via high-precision interval/MPFR arithmetic (`searchreals.rkt`, `points.rkt`).
2. **Error localization & patching**: Localizes subexpressions with highest ULP error (`localize.rkt`), applies e-graph/egglog algebraic rewrites (`egg-herbie.rkt`, `egglog-herbie.rkt`, `rules.rkt`) and Taylor series expansions around $0$ or $\infty$ (`taylor.rkt`, `taylor-cover.rkt`).
3. **Regime inference (`make-regime!`, `regimes.rkt`)**: Partitions the input domain into piecewise intervals and splices together the lowest-error candidate expression per regime using `if` branches.

Probe 1C quantifies Herbie's textbook catastrophic-cancellation rewrite $\sqrt{x+1} - \sqrt{x} \leadsto \frac{1}{\sqrt{x+1} + \sqrt{x}}$ in `binary64`:

| Input $x$ | Naive $\sqrt{x+1} - \sqrt{x}$ (`binary64`) | Naive Relative Error | Rationalized $\frac{1}{\sqrt{x+1}+\sqrt{x}}$ | Rationalized Relative Error |
|---|---|---|---|---|
| $10^{4}$ | `4.9998750062485442e-03` | `2.130e-13` | `4.9998750062496093e-03` | `1.726e-17` |
| $10^{8}$ | `5.0000000555883162e-05` | `1.362e-08` | `4.9999999874999996e-05` | `9.011e-17` |
| $10^{12}$ | `5.0000380724668503e-07` | `7.614e-06` | `4.9999999999987493e-07` | `1.317e-16` |
| $10^{15}$ | `1.8626451492309570e-08` | `1.780e-01` (17.8%) | `1.5811388300841893e-08` | `3.809e-18` |
| $10^{16}$ | `0.0000000000000000e+00` | `1.000e+00` (100% loss) | `5.0000000000000001e-09` | `4.592e-17` |

**Soundness boundary**: Herbie optimizes empirical bits-of-error over sampled points and provides **no worst-case soundness proof**—unsampled singularities, narrow cancellation valleys, or branch-point discontinuities introduced by regime inference can exhibit arbitrarily large errors outside the sample set. Pair Herbie rewriting with a sound verifier (`Daisy`, `FPTaylor`, or `VCFloat2`) before relying on rewritten code in safety-critical paths.

#### 3.3 Symbolic Taylor Bounds (`FPTaylor`), In-Coq Verification (`VCFloat2`), and Graded Error Types (`NumFuzz`, `Bean`)
Basis: source (`soarlab/FPTaylor@b5a77cae34`, `VeriNum/vcfloat@a203b287a8`, `ak-2485/NumFuzz@80c54f3534` & `bean@e100727bf2`) + documentation (Solovyev et al., *TOPLAS* 2018; Appel & Kellison, CPP 2024; Kellison & Hsu, PLDI 2024 `10.1145/3656456`; Kellison et al., PLDI 2025 `10.1145/3729324`)

- **FPTaylor (`soarlab/FPTaylor@b5a77cae34`)**: Formulates roundoff error via **Symbolic Taylor Expansions**—treating each operation's rounding error $\delta_i$ as an independent bounded variable and expanding the output error to first order in $\delta_i$ plus a sound second-order remainder bounded by global branch-and-bound optimization (`b_and_b/opt0.ml`). Crucially, FPTaylor generates independently checkable **HOL Light proof certificates** (`formal/README.md`, `formal/build_tform.hl`, `formal/bin_float.hl`) verified via the `formal_ineqs` nonlinear inequality checker (though loading HOL Light multivariate analysis takes up to ~2 hours without DMTCP checkpointing, `formal/README.md:L55-L60`).
- **VCFloat2 (`VeriNum/vcfloat@a203b287a8`)**: Performs foundational roundoff verification **directly inside Coq** atop Flocq and CompCert's IEEE-754 floating-point formalization (`vcfloat/FPLang.v:L4-L103`). `FPLang.v` distinguishes `Rounded2` binary ops (with optional `Normal`/`Denormal` rounding knowledge), exact `SterbenzMinus`, exact `PlusZero`, exact unary ops (`Abs`, `Opp`, `Shift`), `Cast`, and extensible `Func (f: floatfunc_package ty)` packages for elementary/library functions (`L30-L103`), discharging interval goals via CoqInterval (`Interval.Tactic`) and connecting directly to CompCert/VST C program proofs.
- **NumFuzz (`ak-2485/NumFuzz@80c54f3534`, PLDI 2024) and Bean (`e100727bf2`, PLDI 2025)**: Embed rounding error directly into linear/sensitivity **type systems** based on Olver's relative precision metric $\text{RP}(x, y) = |\ln(x/y)|$ (for same-sign non-zero reals, $0$ at $0$, $\infty$ otherwise).
  - **NumFuzz** combines a sensitivity type system with a graded monad tracking **forward** rounding error compositionally during type checking.
  - **Bean** combines a **graded coeffect system with strict linearity** to track **backward error**—mapping output rounding errors back to equivalent input perturbations—matching textbook numerical linear algebra backward stability bounds compositionally. Strict linearity is not an accidental restriction: in backward error analysis, an input used twice along distinct computation paths cannot simultaneously absorb two incompatible input perturbations.

#### 3.4 Accuracy Analysis & Rewriting Tool Matrix
Basis: source + documentation + derived synthesis

| System (Pinned Revision) | Guarantee Kind | Primary Method | Branches / Loops | Machine-Checked Proof / Certificate |
|---|---|---|---|---|
| **Rosa** (`68e58b8c2f`) | Sound worst-case abs error | Interval/Affine + Z3 binary-search tightening | Bounded cross-branch path-divergence check; no unbounded loops | None (untrusted Scala + Z3) |
| **Daisy** (`6a6f47abdd`) | Sound worst-case abs/rel error + mixed-prec | IA / AA / SMT / FPTaylor / subdivision | Conditional path tracking; modular functions & arrays | Optional Coq / HOL4 / CakeML certifier (Becker et al., FMCAD 2018) |
| **FPTaylor** (`b5a77cae34`) | Sound worst-case abs/rel/ULP | First-order Symbolic Taylor + global B&B | Straight-line expressions (FPCore / FPTaylor DSL) | HOL Light proof certificates (`formal/build_tform.hl`) |
| **VCFloat2** (`a203b287a8`) | Machine-checked foundational bound | Symbolic error terms + CoqInterval + Flocq | Straight-line exprs composed inside Coq/VST proofs (C loops via VST) | Full Coq kernel proof (Composes with CompCert/VST) |
| **NumFuzz** (`80c54f3534`) | Sound compositional forward error (RP) | Sensitivity type system + graded monad | Restricted control flow; linear/affine sensitivity discipline | Paper metatheory (categorical semantics); OCaml typechecker |
| **Bean** (`e100727bf2`) | Sound compositional backward error (RP) | Graded coeffect system + strict linearity | First-order linear programs (dense linear algebra kernels) | Paper metatheory (triple-transformation semantics); OCaml typechecker |
| **Herbie** (`4612b0d493`) | **Unsound** empirical reduction | Sampling + e-graph/egglog + Taylor + regimes | Synthesizes piecewise `if` regimes | None (empirical sampling only) |

---

### 4. Compiler Floating-Point Semantics, Fast-Math Hazards, and Verified Compilers

#### 4.1 Value-Unsafe Flags Destroy Numerical Algorithms (`gcc 15.2.0` Execution Proof)
Basis: execution (Probe 1E under Evidence on `gcc (Debian 15.2.0-14) 15.2.0`) + documentation (Monniaux, *TOPLAS* 2008; Boldo et al., *JAR* 2015; Becker et al., CAV 2019)

Even when source code is proved accurate under strict IEEE-754 arithmetic, compiler flags routinely invalidate the proof during lowering (Monniaux 2008):
1. **Reassociation deletes error compensation**: Kahan compensated summation computes `y = x[i] - c; t = sum + y; c = (t - sum) - y; sum = t;` to recover low-order rounding bits lost in `sum + y`. Running Probe 1E summing `1e16` followed by $10^6$ copies of `1.0` (exact sum `10000000001000000.0`) yields:
   - `gcc -O2 -ffp-contract=off`: **`10000000001000000.0` (`err = 0.0`)**; generated `kahan_sum` loop preserves all four scalar operations (`subsd`, `addsd`, `subsd`, `subsd`).
   - `gcc -O3 -ffast-math`: **`10000000000500000.0` (`err = -500000.0`)**; GCC algebraically simplifies `(sum + y) - sum - y` to `0.0`, deletes `c` completely, and auto-vectorizes the loop into raw `addpd` + `addsd`!
2. **FMA contraction breaks symmetric cancellation**: Evaluating `a*b - c*d` with `a = b = c = d = 1.0 + 2^-27` yields:
   - `gcc -O2 -ffp-contract=off`: **`0.00000000000000000e+00`** (both products rounded identically before subtraction).
   - `gcc -O2 -mfma -ffp-contract=fast`: **`5.55111512312578270e-17`** ($\ne 0$, because GCC rounds one product `a*a` and fuses the other with subtraction via FMA, exposing the exact rounding residual of `a*a`!).

#### 4.2 CompCert Strict Semantics vs. Icing Nondeterministic Fast-Math
Basis: source (`AbsInt/CompCert@2685140bf7`) + documentation (Boldo, Jourdan, Leroy, Melquiond, *JAR* 2015; Becker, Darulova, Myreen, Tatlock, CAV 2019)

Verified compilers resolve this tension in two complementary ways:
- **CompCert (`AbsInt/CompCert@2685140bf7`)**: Pins IEEE-754 semantics formalized in Coq/Flocq (`Flocq` binary floats with explicit target NaN canonicalization), forbidding reassociation and unintended contraction so source-level proofs (e.g., VCFloat2/VST) transfer directly to assembly.
- **Icing (CAV 2019, built atop CakeML)**: Introduces scoped `opt:` blocks whose big-step semantics `(cfg, E, e) -> v` evaluates expressions into **delayed value trees** and applies user-selected algebraic rewrites **nondeterministically** (`cfg` carries allowed rewrite rules `s -> t` plus an `OptOk` flag). Icing separates *compiler rewrite preconditions* (required for semantic soundness, e.g., NaN-absence before removing a check) from *application rewrite preconditions* (restricting where rewrites fire so an external analyzer like Daisy/CakeML-certifier can bound worst-case roundoff across all nondeterministic rewrite outcomes).

---

### 5. Elementary Functions (Table-Maker's Dilemma) and Constructive Reals

#### 5.1 IEEE 754-2019 Clause 9, RLibm-All, and CORE-MATH
Basis: source (`rutgers-apl/rlibm-all@90431a0000`, `Cactus-proj/core-math@74fcd1094a`, `README.md`) + documentation (IEEE Std 754-2019 Clause 9; Lim & Nagarakatte, POPL 2021; Sibidanov, Zimmermann, Glondu, IEEE ARITH 2022 `hal-03721525`)

IEEE 754-2019 Clause 5 mandates correct rounding for basic arithmetic (`+`, `-`, `*`, `/`, `sqrt`, `fma`), whereas **Clause 9 ("Recommended operations")** only *recommends* correctly rounded elementary functions (`sin`, `cos`, `exp`, `log`, `pow`, etc.) for conforming implementations. Historically, system `libm` implementations (`glibc`, `musl`, Apple `libSystem`, MSVC `ucrt`) omit correct rounding because of the **table-maker's dilemma**—when $f(x)$ falls extraordinarily close to a midpoint between two representable floats, deciding which way to round requires arbitrary intermediate precision. The result is silent last-bit disagreement across OS libraries and between scalar and SIMD vector math routines, breaking lockstep replica determinism and cross-platform replay.

For any **fixed finite format**, however, the set of inputs is finite, making correct rounding tractable:
- **RLibm / RLibm-All (`rutgers-apl/rlibm-all@90431a0000`, POPL 2021)**: Instead of approximating the mathematical real value $f(x)$ (which wastes polynomial degree on precision beyond rounding intervals), RLibm solves linear-programming constraints to synthesize a single polynomial that falls inside the **rounding interval** of the correctly rounded result for every input, producing correctly rounded outputs across multiple formats (`bfloat16`, `tensorfloat32`, `float32`, posits) and rounding modes simultaneously.
- **CORE-MATH (`Cactus-proj/core-math@74fcd1094a`, ARITH 2022)**: Provides drop-in correctly rounded C implementations (`cr_sin`, `cr_acos`, etc.) for all four IEEE-754 rounding modes. Primary-source inspection of CORE-MATH's documentation (`core-math.gitlabpages.inria.fr` and `README.md`) highlights critical **scope qualifications**:
  1. Univariate `binary32` functions are verified by **exhaustive search** over all $2^{32}$ inputs.
  2. Bivariate functions and `binary64` functions are checked via `--worst` against **known hard-to-round cases** (with dedicated mathematical proofs published progressively for specific routines such as binary64 `acos`/`asin`).
  3. CORE-MATH's core routines explicitly target correct rounding on regular numbers and note they "do not necessarily correctly deal with NaN, infinities or zero, set the underflow and overflow exceptions, nor the inexact flag" unless wrapped/configured appropriately.

#### 5.2 Boehm Constructive Reals: Continuity Wall and Hybrid Symbolic Equality
Basis: documentation (Boehm, PLDI 2020 `10.1145/3385412.3386037`; Boehm et al., LFP 1986 `10.1145/319838.319860`; Richardson, *JSL* 1968; Android `platform/external/crcalc@349dbd732e`) + execution (Probe 1D under Evidence)

Constructive (recursive) reals represent each real number $x \in \mathbb{R}$ as a demand-driven function $\text{approx}(n) : \mathbb{Z} \to \mathbb{Z}$ returning an integer $k$ such that $|k \cdot 2^n - x| < 2^n$ (strictly less than 1 in the least significant requested bit/digit). Operations build lazy expression DAGs with memoized precision caches, guaranteeing that displayed digits never suffer catastrophic cancellation regardless of intermediate cancellation depth.

The fundamental computability wall is **continuity**: by Brouwer/Rice/Richardson (1968), every total computable function $\mathbb{R} \to \{0, 1\}$ is constant, and zero-equivalence is undecidable for expressions built from rationals, $x$, $\pi$, $\ln 2$, $+, -, \times, \sin, \exp, |\cdot|$. Consequently, exact equality (`==`), strict order (`<`), `sign`, and `floor` **cannot be total computable functions on constructive reals**:
- Probe 1D (under Evidence) implements a dyadic constructive-real evaluator for $\sqrt{2}\cdot\sqrt{2}$ versus $2$ and evaluates $|k_a(n) - k_b(n)|$ at $n \in \{10, 50, 100, 500\}$ bits: at every precision, the difference remains `1 <= 1`, so naive iterative precision-doubling **never terminates**.
- **Boehm's PLDI 2020 production architecture (`UnifiedReal` in Android Calculator)**: Solves practical usability without violating computability by layering three representations:
  1. An exact **bounded rational** (`BoundedRational`) when exact rational arithmetic stays within size limits;
  2. A **symbolic multiple of a known irrational/transcendental property tag** (e.g., $q \cdot \pi$, $q \cdot \sqrt{r}$, $q \cdot \ln(r)$ for small rational $q, r$, preserving decidable equality for identities users actually trigger, such as $\sin(\pi) = 0$, $\cos(\pi/2) = 0$, $\sqrt{2}^2 = 2$, $\ln(e) = 1$);
  3. Fallback to lazy **constructive real (`CR`)** evaluation paired with **bounded-precision/tolerance comparison** (`definitelyEquals`/`compareTo` with explicit precision/timeout cutoffs) so comparisons never silently hang an interactive UI or create a denial-of-service vector across FFI.

## Boundaries

- **Not examined**:
  - Stochastic hybrid systems (SDEs / Markov hybrid automata), partial differential equations (PDEs), and neural-network-in-the-loop reachability tools (Flow*, CORA, dReach).
  - Exact cycle-level WCET static analyzers and their formal composition with VeriPhy's dL timing constant $\varepsilon$.
  - Exhaustive differential testing across `glibc`, `musl`, and `llvm-libc` for every transcendental function in IEEE-754 `binary64`.
- **Unknown**:
  - Exact fraction of real-world KeYmaera X nonlinear arithmetic obligations that admit fast kernel-checkable Positivstellensatz / Sum-of-Squares certificates without invoking Mathematica or Z3.
  - Whether a single-prover re-engineering of VeriPhy (e.g., inside Isabelle/HOL or Lean 4 with a verified backend) eliminates all performance regressions compared to HOL4/CakeML extraction.
- **Known not to apply**:
  - **Attractive stronger conclusion rejected**: *"VeriPhy verifies the cyber-physical controller."* — **False.** VeriPhy verifies a *runtime safety sandbox* (`ctrlMon`, `plantMon`, `fallback`) wrapping an *untrusted* controller; it also trusts external QE arithmetic goals (`arith_valid pt`), memory isolation of the untrusted controller, sensor interval soundness, and a hand-translated Isabelle-to-HOL4 bridge.
  - **Attractive stronger conclusion rejected**: *"Herbie guarantees improved worst-case floating-point accuracy."* — **False.** Herbie optimizes sampled ULP error and can worsen accuracy on unsampled points or near inferred regime boundaries.
  - **Attractive stronger conclusion rejected**: *"CORE-MATH functions are full drop-in IEEE-754 replacements including exception flags and special values."* — **False** without wrappers; upstream documentation explicitly states core routines focus on correct rounding of regular numbers and do not necessarily set underflow/overflow/inexact flags or handle all NaN/Inf edge cases.
- **Unsupported**:
  - Exact decidable zero-crossing detection for arbitrary computable real guards $g(x(t)) = 0$ (mathematically impossible; only $\varepsilon$-tolerance/transversality-qualified detection is computable).
  - Decidable total equality (`==`) on unrestricted constructive reals (undecidable by Richardson's theorem, 1968).
  - Unbounded loops and arbitrary aliasing in NumFuzz/Bean without violating sensitivity/linearity typing invariants.

## Evidence

### Primary Git Repositories & Source Anchors (Observed 2026-11-19)
- **`INRIA/zelus`** (`5f6e4903103e136f52cdcefc13a9bdcff0f53abd`):
  - `compiler/global/deftypes.ml:L66-L106` — `kind` (`Tstatic`, `Tany`, `Tcont`, `Tdiscrete`, `Tproba`) and `mkind` (`Cont`, `Zero`, `Horizon`, `Period`, `Encore`, `Major`).
  - `compiler/analysis/causality.ml:L17-L180` — `C | H |-cfree e : ct` strict partial-order causality inference, `Causal.Clash` cycle diagnostics, tuple vs. atomic record treatment.
  - `compiler/main/simulator.ml:L39-L160` — discrete vs. continuous simulation driver typing.
- **`inria-parkas/sundialsml`** (`27ae63cf9e6e45e4b820232d99366751e30a6b9f`): `README.md` — OCaml bindings to SUNDIALS CVODE/IDA/ARKODE solvers.
- **`modelica/fmi-standard`** (`fff9c88a58e61cf8d71f1992457288bb3399460c`): `docs/2_2_common_mechanisms.adoc:L334-L672` — FMI 3.0 `fmi3Clock` super-dense time synchronization and optional `canGetAndSetFMUState` (`L575`) / `canSerializeFMUState` (`L608`) rollback capability flags.
- **`LS-Lab/KeYmaeraX-release`** (`2753f99b53cea5f946386998a39faded05ede677`):
  - `keymaerax-core/src/main/scala/org/keymaerax/core/Proof.scala:L188-L640,L873` — `Provable` kernel, `trustedTools` whitelist (`MathematicaQETool`, `Z3QETool`, `BigDecimalQETool$`, `L515-L516`), `proveArithmetic` oracle invocation (`L601-L610`), `vectorialDG` (`L626-L640`).
  - `keymaerax-core/src/main/scala/org/keymaerax/core/QETool.scala:L10-L21` and `keymaerax-core/src/main/scala/org/keymaerax/btactics/ModelPlex.scala`.
- **`LS-Lab/Isabelle-dL`** (`97770ed9ca8d6a633c59d11d799247f44cc62dc2`):
  - `Interval_Arithmetic.thy:L11-L95,L5007-L5039` — 32-bit signed word intervals excluding `0x80000000`, `repe`/`repU`/`repL`/`repP`, `theorem fixed_point_sound`.
  - `Proof_Checker.thy:L5343-L5635` — `sound_to_valid`, `DIAnd_sound`.
- **`LS-Lab/Coq-dL`** (`af7e7dc5cc44f8a3e24b2a6a154bfff7858dfb2b`) & **`CakeML/cakeml`** (`2874b664e10939a3ee462215b2e068c89c1f70eb`).
- **`malyzajko/daisy`** (`6a6f47abdd231d3009444e9e1b8ce9febc28c27e`): `README.md:L73-L141` (Tree-sitter `.scala`/`.c`/`.fpcore` frontends), `src/main/scala/daisy/tools/RoundoffEvaluators.scala:L26-L160` (`uniformRoundoff_{IA,AA,SMT}_AA`, `sterbenzTheoremApplies`).
- **`malyzajko/rosa`** (`68e58b8c2f334ddde0f7647dc2d9c9ecc30309af`).
- **`herbie-fp/herbie`** (`4612b0d493cbb2013dc5afac5c099b7722166ec2`): `src/core/mainloop.rkt:L39-L88` (`run-improve!`, `make-regime!`, sampling/validation contexts) and `src/core/egglog-herbie.rkt`.
- **`FPBench/FPBench`** (`090d81982edc0d2a597f4c15644253d4f266a6ef`).
- **`soarlab/FPTaylor`** (`b5a77cae348400f21f83512210d9f43c4bffb381`): `formal/README.md` (HOL Light + `formal_ineqs` certificate checking).
- **`VeriNum/vcfloat`** (`a203b287a84b0e3c9bec136823b5622ebfde6ad6`): `vcfloat/FPLang.v:L30-L180` (`rounded_binop`, `SterbenzMinus`, `PlusZero`, `floatfunc_package`, Flocq/CompCert integration).
- **`ak-2485/NumFuzz`** (`80c54f35348c60b8a1e95f1881adda8d2e9c1dfb`, `bean` branch `e100727bf2441be948e110601b1f566e1fe5815b`): `README.md` and `src/` OCaml typecheckers.
- **`rutgers-apl/rlibm-all`** (`90431a000071e415abf0f403b6125c385551e346`) & **`Cactus-proj/core-math`** (`74fcd1094a316164c94481f40f5c9658439bee63`, `README.md`) & **`AbsInt/CompCert`** (`2685140bf72c959446981fb99b5e44a8975021bc`).

### Peer-Reviewed Literature & Standards
- T. Bourke & M. Pouzet, *Zélus: A Synchronous Language with ODEs*, HSCC 2013, `10.1145/2461328.2461348`.
- R. Bohrer, Y. K. Tan, S. Mitsch, M. O. Myreen, A. Platzer, *VeriPhy: Verified Controller Executables from Verified Cyber-Physical System Models*, PLDI 2018, `10.1145/3192366.3192406` (full PDF text verified from `https://symbolaris.com/pub/VeriPhy.pdf`).
- E. Darulova & V. Kuncak, *Sound Compilation of Reals*, POPL 2014 (`arXiv:1309.2511`).
- H. Becker, N. Zyuzin, R. Monat, E. Darulova, M. O. Myreen, A. Fox, *A Verified Certificate Checker for Finite-Precision Error Bounds in Coq and HOL4*, FMCAD 2018 (`arXiv:1707.02115`).
- H. Becker, E. Darulova, M. O. Myreen, Z. Tatlock, *Icing: Supporting Fast-Math Style Optimizations in a Verified Compiler*, CAV 2019 (`https://malyzajko.github.io/papers/cav2019a.pdf`).
- A. E. Kellison & J. Hsu, *Numerical Fuzz: A Type System for Rounding Error Analysis*, PACMPL 8 (PLDI 2024), `10.1145/3656456` (`arXiv:2405.04612`).
- A. E. Kellison, L. Zielinski, D. Bindel, J. Hsu, *Bean: A Language for Backward Error Analysis*, PACMPL 9 (PLDI 2025), `10.1145/3729324` (`arXiv:2501.14550`).
- H.-J. Boehm, *Towards an API for the Real Numbers*, PLDI 2020, `10.1145/3385412.3386037`; H.-J. Boehm et al., LFP 1986, `10.1145/319838.319860`.
- A. Sibidanov, P. Zimmermann, S. Glondu, *The CORE-MATH Project*, IEEE ARITH 2022 (`hal-03721525`).
- IEEE Std 754-2019, Clauses 5 & 9 (required vs. recommended correctly rounded operations).

### Local Execution Probes (2026-11-19, x86_64 Linux, Python 3.13, GCC 15.2.0)
- **Probe 1A (Zeno & zero-crossings)**: Bouncing ball ($h_0=1, g=9.81, e=0.5$) hit 1000-bounce cutoff at $t_\infty = 1.3545709230\,\text{s}$ across `dt ∈ {1e-2, 1e-3, 1e-4}`; $g_{\text{even}}(t) = (t-0.5)^2 - 0.002^2$ detected at `t0=0.450, h=0.01` (`[(0.49, 0.5), (0.5, 0.51)]`) and missed completely at `t0=0.455, h=0.01` (`[]`); $g_{\text{tang}}(t)=(t-0.5)^2$ missed on all grids.
- **Probe 1B (VeriPhy 32-bit integer intervals)**: `d=(505,515)` $\to$ `True`, `d=(498,508)` $\to$ `Unknown` (fallback), `x-x` on `(10,12)` $\to$ `(-2,2)` (`Unknown`).
- **Probe 1C (Cancellation, path divergence, IA vs. AA)**: $\sqrt{x+1}-\sqrt{x}$ relative error reached `1.000e+00` at $x=10^{16}$ vs. `4.592e-17` rationalized; `0.1+0.2-0.3` flipped discontinuous branch causing `abs_err = 2.0`; `x*(1-x)` on `[0.4, 0.6]` gave IA width `0.20` vs. AA width `0.02` vs. exact `0.01`.
- **Probe 1D (Constructive reals)**: $|k(\sqrt{2}\cdot\sqrt{2}) - k(2)| = 1 \le 1$ remained undecided at $n = 10, 50, 100, 500$ bits.
- **Probe 1E (`gcc 15.2.0` fast-math & FMA contraction)**:
  Minimal C reproducer compiled with `gcc -O2 -ffp-contract=off`, `gcc -O2 -mfma -ffp-contract=fast`, and `gcc -O3 -ffast-math`:
  ```c
  __attribute__((noinline)) double kahan_sum(const double *xs, size_t n) {
    double sum = 0.0, c = 0.0;
    for (size_t i = 0; i < n; i++) {
      double y = xs[i] - c, t = sum + y; c = (t - sum) - y; sum = t;
    }
    return sum;
  }
  __attribute__((noinline)) double det2(double a, double b, double c, double d) {
    return a * b - c * d;
  }
  ```
  Inputs: `xs = [1e16, 1.0, ..., 1.0]` (`n = 1000001`), `a = b = c = d = 1.0 + ldexp(1.0, -27)` (via `volatile double`).
  - `gcc -O2 -ffp-contract=off`: `kahan_sum` err `0.0` (4 scalar FP ops preserved: `subsd`, `addsd`, `subsd`, `subsd`), `det2` = `0.0`.
  - `gcc -O2 -mfma -ffp-contract=fast`: `det2` = `5.55111512312578270e-17`.
  - `gcc -O3 -ffast-math`: `kahan_sum` collapsed to `addpd`/`addsd`, err = `-500000.0`.

## Revalidation

1. **Check KeYmaera X QE oracle boundary**: Diff `keymaerax-core/src/main/scala/org/keymaerax/core/Proof.scala` around `trustedTools` and `proveArithmetic` on newer `LS-Lab/KeYmaeraX-release` tags to see whether certificate-producing real QE (e.g., SOS/Positivstellensatz) has replaced `oracle(...)`.
2. **Check Zélus kinding & FMI rollback evolution**: Diff `INRIA/zelus` `compiler/global/deftypes.ml` (`kind`, `mkind`) and `modelica/fmi-standard` `docs/2_2_common_mechanisms.adoc` around `canGetAndSetFMUState` and `Clock` if adopting a newer FMI 3.x minor release.
3. **Re-run C fast-math & FMA compiler probe**: Recompile a 20-line Kahan summation + `a*a - a*a` (`a = 1 + 2^-27`) test under the target compiler (`-O2 -ffp-contract=off`, `-O2 -mfma -ffp-contract=fast`, `-O3 -ffast-math`) and inspect assembly (`-S`) on any compiler upgrade or architecture change (e.g., ARM64 where FMA contraction defaults can differ).
4. **Re-check CORE-MATH & VeriPhy successor proofs**: Check `Cactus-proj/core-math` / `gitlab.inria.fr/core-math/core-math` status tables for newly proved `binary64` functions and special-value compliance, and check successor papers to VeriPhy (PLDI 2018) to verify whether the hand-translated Isabelle-to-HOL4 bridge or arithmetic-oracle TCB item has been eliminated.
