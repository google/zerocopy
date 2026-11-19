# Floating-Point Accuracy Synthesis, Symbolic Taylor Round-Off Enclosures, and Certified Proof Bridges

## Summary

Automated floating-point accuracy synthesis (`Herbie`) and sound worst-case round-off verification (`FPTaylor`, `Daisy`, `Gappa`, `LeanCert`) solve complementary halves of finite-precision numerical engineering over the common `FPCore` (`FPBench`) specification language, and neither is sufficient in isolation:

1. **Sampling-Guided Accuracy Rewriting Is Empirical and Can Introduce Non-Real Traps (`Herbie`):** `Herbie` (`herbie-fp/herbie`) localizes single-operation ULPs lost to catastrophic cancellation against arbitrary-precision `rival` real-interval ground truth, expands candidates through e-graph equality saturation (`egg`/`egglog`) plus asymptotic series (`taylor.rkt`), and stitches input-domain intervals via dynamic-programming Pareto regime inference (`regimes.rkt`). Because candidate ranking minimizes average sample bit-error over finitely many points rather than proving worst-case enclosures, $\mathbb{R}$-equivalent rewrites exhibit three hazardous failure modes unless certified downstream: (a) **intermediate IEEE 754 exponent overflow** ($\sqrt{x^2+1}-x \leadsto \frac{1}{\sqrt{x^2+1}+x}$ overflows $x^2 > \text{DBL\_MAX}$ to $+\infty$ at $x = 10^{160}$, silently underflowing the reciprocal to `+0.0` with 60.9 bits of error); (b) **signed-zero (`-0.0`) polarity flips** ($\text{expm1}(-0.0) = -0.0$ vs. $\exp(-0.0) - 1 = +0.0$, flipping $1/f(-0.0)$ from $-\infty$ to $+\infty$); and (c) **regime-boundary non-monotonicity**, where splicing a Taylor polynomial $P_3(x)$ against a library call across split threshold $s$ creates a strictly decreasing step on a strictly increasing real function.
2. **First-Order Symbolic Taylor Forms Defeat the Correlated-Error Dependency Problem (`FPTaylor` & `Daisy`):** Naive interval and affine round-off analyses propagate value ranges and error terms separately, double-counting correlated variables in quotients and transcendentals (e.g., overapproximating the round-off error of $\frac{x}{x+1}$ on $[1, 2]$ by $1.875\times$). Symbolic Taylor forms (`taylor_form.ml` in `FPTaylor`, `Taylor.scala` in `Daisy`) expand the finite-precision execution $\hat{f}(x, \vec{\epsilon}, \vec{\delta})$ to first order around $(\vec{\epsilon}, \vec{\delta}) = (\vec{0}, \vec{0})$, preserving exact symbolic real partial derivatives $\frac{\partial \hat{f}}{\partial \epsilon_i}(x, \vec{0}, \vec{0})$ so correlated sensitivities cancel algebraically prior to global branch-and-bound maximization, while rigorously enclosing all higher-order cross terms in a quadratic Lagrange remainder $M_2$.
3. **Subnormal Underflow (`FTZ`/`DAZ`) Splits Proof Models Between `FPTaylor` and `Daisy`:** Standard IEEE 754 gradual underflow satisfies $|\text{RN}(x) - x| \le |x|\cdot 2^{-53} + 2^{-1075}$ in `binary64` (`Daisy` `Float64.denormalsError = 2^-1075`) and exactness of same-precision addition/subtraction in the subnormal range ($\delta = 0$ by Hauser's theorem). Direct source inspection reveals a critical dual subtlety in `soarlab/FPTaylor`: its built-in `rnd64` table (`rounding.ml:61`, `formal/build_tform2.hl:48`) sets default `delta_exp = -1022` ($2^{-1022} = 2^{e_{\min}}$, because OCaml `float` underflows $2^{-1075}$ to `0.0`), yet `rounding_simpl.ml:114-120` simultaneously rewrites `Op_add`/`Op_sub` to `delta_exp = 0`. Consequently, `FPTaylor`'s default bounds are $2^{53}\times$ conservative on subnormal products, yet **still unsound on hardware with Flush-To-Zero (`FTZ`) or Denormals-Are-Zero (`DAZ`) enabled**, where normal-operand subtraction ($1.5\times 2^{-1022} - 1.0\times 2^{-1022}$) flushes to `0.0` with error $2^{-1023} \neq 0$.
4. **FMA Contraction Eliminates Product Rounding Yet Breaks Symmetric Cancellation:** `FPTaylor` models `rnd64(fma(a, b, c))` by composing exact `mul_form` and `add_form` inside a single outer `rounded_form` (`taylor_form.ml:714-716, 760`). However, compiler `-ffp-contract=fast` rewriting symmetric $x^2 - y^2$ into asymmetric `fma(x, x, -(y * y))` destroys exact cancellation at $x = y$ whenever $\text{RN}(y^2) > y^2$: at $x = y = 1 + 5\cdot 2^{-28}$, uncontracted $\sqrt{x^2 - y^2} = 0$, whereas FMA-contracted $\sqrt{\text{fma}(x, x, -(y\cdot y))}$ evaluates to **`-nan`**.
5. **Certificate TCB Isolation Requires Explicit Kernel-Mode Verification (`HOL Light` & `LeanCert`):** `FPTaylor`'s HOL Light certificate exporter (`proof-record = true`) rejects `fp-power2-model = true` and `develop = true` (`fptaylor.ml:649-661`), disabling Sterbenz `sub2` cancellation and binade `p2max` tightening during certified runs. In Lean 4 (`alerad/leancert`), rational/dyadic interval certificates default to `leancert.trust = "native"` (and `"auto"` silently falls back above calibrated term/partition/iteration thresholds), introducing the compiler-trusting `Lean.ofReduceBool` (`native_decide`) axiom unless callers explicitly enforce `set_option leancert.trust "kernel"`.

## Applicability

This report covers floating-point rewrite synthesis, static worst-case round-off error bounding, mixed-precision/fixed-point code generation, and proof-producing numerical enclosure checking across five pinned upstream repositories and four peer-reviewed specifications:

- **`herbie-fp/herbie`** at commit `4612b0d493cbb2013dc5afac5c099b7722166ec2` (implementing and extending Panchekha et al., PLDI 2015, `DOI: 10.1145/2737924.2737959`): Racket-based floating-point expression optimizer combining `rival` real-interval evaluation, e-graph equality saturation (`egg`/`egglog`), series expansion, and Pareto regime splicing.
- **`soarlab/FPTaylor`** at commit `b5a77cae348400f21f83512210d9f43c4bffb381` (implementing Solovyev et al., ACM TOPLAS 2018, `DOI: 10.1145/3230733`): OCaml static analyzer computing sound absolute, relative, and ULP round-off enclosures via first-order Symbolic Taylor forms, internal interval branch-and-bound (`opt_basic_bb.ml` / `gelpia` / `z3`), and HOL Light formal certificate scripts (`formal/`).
- **`malyzajko/daisy`** at commit `6a6f47abdd231d3009444e9e1b8ce9febc28c27e` (implementing Darulova et al., TACAS 2018, `DOI: 10.1007/978-3-319-89960-2_15`): Scala modular numerical verification and synthesis framework implementing dataflow interval/affine error propagation, domain subdivision, Symbolic Taylor error phases, genetic rewriting, mixed-precision tuning, and Scala/C/Vivado-HLS `ap_fixed` code generation.
- **`FPBench/FPBench`** at commit `090d81982edc0d2a597f4c15644253d4f266a6ef`: standard `FPCore` S-expression IR, rounding-context metadata (`:precision`, `:round`, `:pre`), and benchmark corpus shared across `Herbie`, `FPTaylor`, and `Daisy`.
- **`alerad/leancert`** at commit `44b323a0d6af00211d5013f6e021432db032087c`: Lean 4 certified numerics library providing interval/dyadic/affine/Taylor real bounds, branch-and-bound global optimization, and configurable `kernel` vs. `native` certificate bridge tactics (`LeanCert/Tactic/Verification.lean`).
- **Gappa Forward Error & Proof Specification** (Daumas and Melquiond, ACM TOMS 2010, `DOI: 10.1145/1644001.1644002`): interval + forward error rewriting calculus exporting Coq (`Flocq`) and HOL Light proofs for rounded fixed/floating-point expressions.

In a sound synthesis-and-verification workflow, `FPCore` specifications with domain preconditions (`:pre`) flow into `Herbie` (or `Daisy --rewrite`) as an **untrusted oracle** proposing candidate piecewise rewrites, after which each regime branch—intersected with the exact floating-point guard interval—must be discharged independently by `FPTaylor`, `Daisy`, `Gappa`, or `LeanCert` (`trust := kernel`).

## Findings

### 1. Sampling-Guided Cancellation Localization, Equality Saturation, and Regime Splicing in `Herbie`

`Basis: normative + source + execution`

#### 1.1 Ordinal Bits-of-Error Metric and Local Error Attribution (`localize.rkt`)

Given an input point $\vec{x} \in \mathbb{F}^n$ sampled over precondition `:pre` (`src/core/sampling.rkt`), `Herbie` evaluates the candidate floating-point program $\hat{e}(\vec{x})$ in target representation `repr` (e.g., IEEE 754 `binary64`, `binary32`, or custom `platform` types) and computes the exact real semantics $e_{\mathbb{R}}(\vec{x})$ via `rival` (`src/platforms/rival.rkt`), an adaptive arbitrary-precision MPFR interval evaluator that widens precision until the rounded target float $\text{RN}(e_{\mathbb{R}}(\vec{x}))$ is uniquely determined.

Accuracy loss is measured in **bits of error** (`repr-error`, `src/syntax/types.rkt`): mapping each finite IEEE 754 bit-pattern $z \in \mathbb{F}$ monotonically onto its signed-magnitude integer rank $\text{ord}_{\mathbb{F}}(z) \in \mathbb{Z}$, the error between computed float $\hat{y}$ and ideal rounded float $y^* = \text{RN}(y_{\mathbb{R}})$ is:

$$\text{err}_{\text{bits}}(\hat{y}, y^*) = \log_2\left(1 + \left|\text{ord}_{\mathbb{F}}(\hat{y}) - \text{ord}_{\mathbb{F}}(y^*)\right|\right) \in [0, w]$$

where $w = 64$ for `binary64` (`0` bits = bit-exact `0 ULP`; `1` bit = `1 ULP`; `53+` bits = complete significand loss or overflow to `Inf`).
- **Subexpression Localization (`src/core/localize.rkt:139-215`):** Rather than rewriting every AST node blindly, `compute-errors` evaluates both exact real values `exacts` and floating-point values `actuals` at every subexpression $v = \text{op}(u_1, \dots, u_k)$, then computes single-step **local error** (`local-error`, `L196`): the ULP distance between $\text{op}_{\mathbb{F}}(\text{RN}(u_{1,\mathbb{R}}), \dots, \text{RN}(u_{k,\mathbb{R}}))$ and $\text{RN}(\text{op}_{\mathbb{R}}(u_{1,\mathbb{R}}, \dots, u_{k,\mathbb{R}}))$. Subtrees with high local error pinpoint catastrophic cancellation (`a - b` where $a \approx b$ shifts uncomputed low bits into leading mantissa positions) or single-op overflow. *(Implementation detail at `localize.rkt:125-136`: `remove-infinities` replaces non-rational/infinite values with `0.bf` when building `delta-ctx` so absolute-difference diagnostics `fabs(spec - var)` do not NaN-poison unrelated columns.)*

#### 1.2 E-Graph Rewrite Synthesis, Series Expansion, and Pareto Regime Inference

`Herbie`'s `mainloop.rkt` iterates three candidate-generation engines before regime splicing:
1. **Equality Saturation (`src/core/egg-herbie.rkt`, `src/core/egglog-herbie.rkt`):** Encodes subexpressions localized for high error into an e-graph (`Willsey et al., POPL 2021`, `DOI: 10.1145/3434304`) populated with sound $\mathbb{R}$-algebraic, trigonometric, exponential/logarithmic, and special-intrinsic rules (`src/core/rules.rkt`, e.g., $\sqrt{a} - \sqrt{b} \leftrightarrow \frac{a - b}{\sqrt{a} + \sqrt{b}}$, $e^x - 1 \leftrightarrow \text{expm1}(x)$, $\ln(1 + x) \leftrightarrow \text{log1p}(x)$), extracting minimum-cost forms that eliminate cancellation nodes.
2. **Asymptotic Series Expansion (`src/core/taylor.rkt`, `src/core/taylor-cover.rkt`):** Around removable singularities ($x \to 0$, $x \to \pm\infty$) where algebraic rearrangement fails—such as $\frac{e^x - 1}{x} \approx 1 + \frac{x}{2} + \frac{x^2}{6} + \frac{x^3}{24}$ or $\sqrt{x^2 + 1} - x = x(\sqrt{1 + x^{-2}} - 1) \approx \frac{1}{2x} - \frac{1}{8x^3}$—`Herbie` computes symbolic Puiseux/Laurent/Taylor expansions directly in Horner form.
3. **Pareto Regime Splicing (`src/core/regimes.rkt:41-260`):** No single branch is accurate everywhere (Taylor series diverge away from the expansion center; rationalized algebraic forms overflow at extreme magnitudes). Given candidate vector `alts-vec` (`L43`) and sampled point matrix `errors` (`L45-46`), `pareto-regimes` sorts sample indices along candidate branch expressions `branch-vs` (`L52-56`) and runs dynamic programming (`infer-option`, `L125`) over split thresholds `can-split` to compute the Pareto frontier trading branch complexity (`if`/`<=` cost) against sample-mean bit error.

#### 1.3 Three $\mathbb{R}$-Identity Soundness Traps in Uncertified `Herbie` Rewrites

`Basis: execution + derived`

Because `Herbie` optimizes over a finite random sample ($N_{\text{pts}} = 256$ by default, evaluated at $8000$ test points) under real-number rewrite rules, three failure classes arise when deploying `Herbie` outputs without formal range/error verification (all three verified by Executable Probe 1 in Evidence):

1. **Intermediate Exponent Overflow Masking as Silent Zero Underflow:**
   For $f(x) = \sqrt{x^2 + 1} - x$ on $x > 0$:
   - At $x = 10^8$, naive `sqrt(x*x + 1.0) - x` evaluates `sqrt(1e16 + 1.0) == 1e8` (`1.0 < 0.5 ulp(1e16) = 1.0`), returning `0.0` (**62.0 bits of error**), whereas rationalized `1.0 / (sqrt(x*x + 1.0) + x)` returns `5e-09` (**0.0 bits of error**).
   - At $x = 10^{160}$, exact $f(10^{160}) \approx 5 \times 10^{-161}$ is a normal `binary64` float ($> 2^{-1022} \approx 2.225 \times 10^{-308}$). Yet `x * x` exceeds $\text{DBL\_MAX} \approx 1.7977 \times 10^{308}$ and overflows to `+inf`. While the naive form visibly overflows to `+inf`, the rationalized rewrite evaluates `1.0 / (+inf + 1e160) == +0.0`—**silently returning zero with 60.9 bits of error and no NaN!** Only splicing an asymptotic high-magnitude regime (`if x > 2^27 then 0.5 / x`) or `hypot(x, 1.0)` restores `0.0` bits of error across $(0, 10^{300}]$. If `Herbie`'s input distribution fails to sample $x > \sqrt{\text{DBL\_MAX}} \approx 1.34 \times 10^{154}$, regime inference omits the upper split.
2. **Signed-Zero (`-0.0`) Flip and Reciprocal Branch-Cut Inversion:**
   Over $\mathbb{R}$, $e^x - 1 = \text{expm1}(x)$ and $x + 0 = x$. Under IEEE 754 round-to-nearest-even (`Rnd_ne`), `exp(-0.0) - 1.0 == 1.0 - 1.0 == +0.0`, whereas `expm1(-0.0) == -0.0` (preserving odd-function tangent sign $f(-0.0) = -0.0$ per IEEE 754-2019 §9.2). When fed into `1.0 / f(x)` or `atan2(f(x), -1.0)`, `1.0 / (exp(-0.0) - 1.0) == +inf` while `1.0 / expm1(-0.0) == -inf`, inverting discontinuity direction and complex branch cuts ($\pm \pi$).
3. **Regime-Boundary Non-Monotonicity Across Adjacent Floats:**
   Real function $g(x) = e^x - 1$ is strictly increasing ($g'(x) = e^x > 0$). Suppose a synthesized regime splices cubic Horner polynomial $P_3(x) = x(1 + x(\tfrac{1}{2} + \tfrac{x}{6}))$ for $x < s$ with `exp(x) - 1.0` for $x \ge s$ at split point $s = 10^{-5}$. At the predecessor float $s^- = \text{nextafter}(10^{-5}, -\infty)$, $P_3(s^-) = 1.00000500001666665 \times 10^{-5}$, whereas at $s = 10^{-5}$, $\text{RN}(\exp(s) - 1.0) = 1.00000500000696491 \times 10^{-5}$ (because $\exp(10^{-5})$ rounded down to precision $2^{-53} \approx 1.11 \times 10^{-16}$ before subtracting `1.0`). Thus $s^- < s$ yet $\hat{g}(s^-) > \hat{g}(s)$ by **`9.702e-17` (~874 ULPs at $10^{-5}$)**! Spliced regimes violate monotonicity unless split thresholds are placed deep inside the overlapping 0.5-ULP agreement zone where $P_k(s^-) \le \hat{g}_{\text{hi}}(s)$.

---

### 2. Rigorous Symbolic Taylor Forms and Global Optimization in `FPTaylor`

`Basis: normative + source + execution`

#### 2.1 The `(c, eps_exp, delta_exp)` Rounding Model and `fp-power2-model`

`soarlab/FPTaylor` (`DOI: 10.1145/3230733`) axiomatizes every rounded real operation $\text{rnd}(v)$ via the generalized predicate `is_rnd_gen(r, c, e2, d2)` (`formal/rounding.hl:30-41`):

$$\forall v \in \text{dom}:\quad \exists \epsilon, \delta \in \mathbb{R}:\quad |\epsilon| \le e_2 \;\land\; |\delta| \le d_2 \;\land\; \text{rnd}(v) = v + c \cdot \left(r(v)\,\epsilon + \delta\right)$$

- **Standard Linear Envelope (`fp-power2-model = false`, `is_rnd`):** $r(v) = v$, giving the textbook linear bound $|\text{rnd}(v) - v| \le c(|v| e_2 + d_2)$.
- **Binade Power-of-Two Envelope (`fp-power2-model = true`, `is_rnd_bin`):** $r(v) = \text{p2max}(v) = \text{sgn}(v) \cdot \sup\{2^n \mid 2^n < |v|\}$ (`formal/rounding.hl:27-28, 39-40`). For $v = 1.75$ ($2^0 < 1.75 \le 2^1$), $\text{p2max}(1.75) = 1.0$ rather than $1.75$, tightening single-operation rounding bounds by up to $2\times$ near upper binade edges!
- **Rounding Direction Multiplier (`rounding.ml:86-105`):** Round-to-nearest-even (`Rnd_ne`) uses $c = 1.0$ ($e_2 = 2^{-53}$ in `binary64`, i.e., $0.5\text{ ulp}$); directed rounding modes (`Rnd_up`, `Rnd_down`, `Rnd_0`) set `dir_flag = true`, doubling `coefficient` to $2.0 \cdot c$ ($1\text{ ulp}$).
- **Critical Source Discovery on `delta_exp` in `rounding.ml:56-63` vs. `rounding_simpl.ml:114-143`:**
  In `rounding.ml:56-63`, `eps_delta_from_bits` defines default table exponents:
  - `float16`: `(-11, -14)` | `float32`: `(-24, -126)` | `float64`: `(-53, -1022)` | `float128`: `(-113, -16382)`
  confirmed in `formal/build_tform2.hl:48`: ``rnd64(c) = @r. is_rnd_bin (c, ipow2 (-- &53), ipow2 (-- &1022))``. That is, `FPTaylor`'s built-in `rnd64` uses $d_2 = 2^{-1022} = 2^{e_{\min}}$ (the minimum normal float) rather than gradual-underflow half-ULP $2^{-1075}$, because OCaml native `float` arithmetic (`get_eps` in `rounding.ml:159-163`) cannot represent $2^{-1075}$ without underflowing to `0.0`! Users needing tight gradual-underflow bounds on subnormal multiplications must write explicit `rnd[64, ne, 1.0, -53, -1075]`—and even then `get_eps (-1075)` clamps to `ldexp 1.0 (-52 - 1022) = 2^-1074` (`rounding.ml:163`). Meanwhile, `simplify_rounding` (`rounding_simpl.ml:114-143`) sets:
  - `delta_exp = 0` ($\delta = 0$) on exact-type `Op_add`, `Op_sub` (Hauser's gradual-underflow theorem), and `Op_sqrt`;
  - `eps_exp = 0` ($\epsilon = 0$) on multiplication by $2^{-k}$ (`is_neg_power_of_2`, `L126-129`) and division by $2^k$ (`L131-135`, exact mantissa unless underflowing);
  - complete rounding elision (`arg`) on multiplication by $2^k$ (`L122-125`), division by $2^{-k}$ (`L136-138`), and exact subtype casts (`is_subtype`, `L102-104`).

#### 2.2 Compositional `taylor_form` Propagation (`taylor_form.ml`)

A Symbolic Taylor form (`taylor_form.ml:19-30`) represents a rounded subexpression $\hat{e}(x)$ over domain box $X$ as:

$$T_{\hat{e}}(x, \vec{\epsilon}) = v_0(x) + \sum_{(a_k, \text{err}_k) \in v_1,\; \text{index} \ge 0} a_k(x)\,\epsilon_{\text{index}} + \sum_{(m_j, \text{err}_j) \in v_1,\; \text{index} = -1} m_j\,\eta_j$$

where:
- `v0 : expr` is the exact real mathematical expression $e_{\mathbb{R}}(x)$;
- Each indexed entry `(a_k(x), {index = i; exp = e_i})` (`i = find_index original_expr`) tracks the **symbolic real sensitivity expression** $a_k(x)$ multiplying rounding noise variable $|\epsilon_i| \le 2^{e_i}$. Crucially, **identical syntactic rounded subexpressions share the same `index`** (`find_index`), so `merge` (`taylor_form.ml:110-135`) sums or subtracts their symbolic coefficients `(a_k1 + a_k2) * eps_i` directly!
- Anonymous entries with `index = -1` hold conservatively rounded-up floating-point constants (`+^`, `*^` via `Fpu.fadd_high` / `Fpu.fmul_high`, `L47-48`) accumulating additive underflow $\delta$ terms and **second-order Lagrange Taylor remainders** (`m2_err`, `m3_err`).

Compositional propagation rules (`taylor_form.ml:297-765`) run in a single memoized bottom-up DAG pass:
- **Addition / Subtraction (`add_form`, `sub_form`, `L335-348`):** $v_0 = v_{0,1} \pm v_{0,2}$; `merge` combines $v_{1,1}$ and $\pm v_{1,2}$ with zero new second-order remainder.
- **Multiplication (`mul_form`, `L378-389`):** $v_0 = v_{0,1} v_{0,2}$; first-order terms cross-multiply symbolically ($v_{0,1} v_{1,2} + v_{0,2} v_{1,1}$), while the bilinear error product $(\sum a_i \epsilon_i)(\sum b_j \epsilon_j)$ is bounded via outward interval enclosures `sum2_high x1 y1` into an `index = -1` remainder `m2`.
- **Smooth Unary & Transcendental Ops (`uop_form`, `L391-407`):** For $\phi \in \{\text{inv}, \sqrt{\cdot}, \sin, \cos, \tan, \arcsin, \arccos, \arctan, \exp, \ln, \sinh, \cosh, \tanh, \text{arsinh}, \text{arcosh}, \text{artanh}\}$, Taylor's theorem gives $\phi(v_0 + E) = \phi(v_0) + \phi'(v_0) E + \frac{1}{2}\phi''(\xi) E^2$ for $\xi \in v_0(X) + [-|E|_{\max}, |E|_{\max}]$. `uop_form` propagates symbolic $\phi'(v_0) \cdot a_k(x)$ in $v_1$ and bounds $\frac{1}{2}\sup |\phi''(x_0 + s_1)| \cdot E^2$ (`f_high x0_int s1`, e.g., $|\text{inv}''(\xi)|/2 = |\xi|^{-3}$ at `L412`, $|\sqrt{\cdot}''(\xi)|/2 = \frac{1}{8}\xi^{-3/2}$ at `L435-436`) into `m3_err` (`index = -1`).
- **Non-Differentiable `abs`, `max`, `min` (`L600-690`):** Uses exact piecewise interval multiplier `abs_err(t, x)` ($\in \{1\}$ if $x \ge t$, $\{-1\}$ if $x \le -t$, $[-1, 1]$ on $(-t, t)$ where $t \ge |E|$) together with $\max(x, y) = \frac{|x-y| + x + y}{2}$ (`L642-643`) to propagate Symbolic Taylor forms across non-smooth kinks without exploding subcases!

#### 2.3 Exact Global Optimization Objective (`fptaylor.ml`)

Splitting `tf.v1` into indexed first-order terms `v1` and constant higher-order remainders `v2` (`total2_i`), `FPTaylor`'s `opt-exact` mode (`fptaylor.ml:280-320, 362-398`) solves a **single real global maximization** over input domain $X$:

$$\text{Err}_{\text{abs}} \le 2^{e_{\text{scale}}} \cdot \max_{x \in X} \sum_{(a_k, \text{err}_k) \in v_1} 2^{\text{err}_k.\text{exp} - e_{\text{scale}}} \left|a_k(x)\right| \;+\; \text{total2}_{\text{high}}$$

(and divides the sum inside $\max_{x \in X}$ by $|v_0(x)|$ for exact relative error, `fptaylor.ml:368`, provided $\inf_{x \in X} |v_0(x)| \ge \text{rel-error-threshold}$). On correlated rational quotient $g(x) = \frac{x}{x + 1}$ over $x \in [1, 2]$, naive forward interval error analysis bounds numerator and denominator errors independently to yield $2.50 u$ ($u = 2^{-53}$), whereas Symbolic Taylor maximizes $\frac{x}{x+1}(|\epsilon_1| + |\epsilon_2|) \le \frac{2}{3}\cdot 2u = 1.333333 u + O(u^2)$—a **$1.875\times$ tightening** within $33.4\%$ of the empirical `binary64` supremum $0.999590 u$ (verified in Executable Probe 2).

---

### 3. Dataflow Subdivision, Mixed-Precision Tuning, and Fixed-Point Synthesis in `Daisy`

`Basis: source`

`malyzajko/daisy` (`DOI: 10.1007/978-3-319-89960-2_15`) generalizes finite-precision verification into a composable compiler pipeline (`DaisyPhase.scala`) spanning two distinct error engines and multi-target hardware codegen:

1. **Forward Dataflow Interval/Affine Engine vs. Symbolic Differentiation Taylor Engine:**
   - **`DataflowPhase` / `AbsErrorPhase`:** Tracks `(realRange: Interval, absError: Rational)` forward at every AST node using Interval Arithmetic, Affine Arithmetic (`AffineForm` retaining linear correlation symbols across additions/subtractions), or SMT-backed `dReal` (`DRealInterpreter.scala`) / Z3 tightening, optionally wrapped in uniform domain box bisection (`DataflowSubdivisionPhase.scala`). Fast ($O(|E|)$ in affine mode), making it tractable inside inner mixed-precision search loops.
   - **`TaylorErrorPhase` (`TaylorErrorPhase.scala:64-110`, `tools/Taylor.scala:56-148`):** Unlike `FPTaylor`'s bottom-up `taylor_form` propagation, `Daisy`'s native `TaylorErrorPhase` constructs the explicit $\epsilon$-$\delta$ Perturbed AST `bodyDelta = epsilonDeltaAbstract(bodyReal, ...)` (`L68`), differentiates `bodyDelta` **symbolically** with respect to each $\epsilon_i$ (`getPartialDerivative`, `Taylor.scala:62`), and bounds the full $O(|\Delta \cup \mathcal{E}|^2)$ Hessian matrix of second partial derivatives $\frac{1}{2}\sum_{u,v} |u \cdot v \cdot \frac{\partial^2 \tilde{f}}{\partial u \partial v}|$ via parallel interval evaluation (`getTaylorRemainder`, `Taylor.scala:74-148`). Because explicit symbolic Hessian construction scales quadratically in the number of rounding sites $m$, `Daisy` also provides `FPTaylorPhase.scala` to delegate larger expressions to bottom-up Taylor forms.
2. **Finite-Precision Lattice, Fixed-Point Bit-Budgeting, and ULP Nuances (`tools/FinitePrecision.scala`):**
   - Models an ordered `Precision` hierarchy (`L10-224`): `Float8` (`(4, 3)`, $\epsilon = 2^{-5}$, $\delta = 2^{-7}$), `Float16` (`(10, 5)`, $\epsilon = 2^{-11}$, $\delta = 2^{-25}$), `Float32` (`(23, 8)`, $\epsilon = 2^{-24}$, $\delta = 2^{-150}$), `Float64` (`(52, 11)`, $\epsilon = 2^{-53}$, $\delta = 2^{-1075}$), software `DoubleDouble` / `QuadDouble`, `FixedPrecision(bitlength)` (`Fixed8`, `Fixed16`, `Fixed32`, `Fixed64`), and Vivado HLS `APFixedType(totalBit, intBits)` (`lang/Types.scala:58`).
   - **Signed Two's-Complement Fixed-Point Bit Sizing (`FinitePrecision.scala:192-223`):** Given real + error range $I$ at an AST node, `integerBitsNeeded(r)` computes `33 - Integer.numberOfLeadingZeros(|r|.integerPart)` (`L199`, reserving 1 sign bit so $|r| = 2^a - 1$ takes $a + 1$ integer bits), assigns remaining `fractionalBits = bitlength - integerBitsNeeded(maxAbs(I))` (`L215`), and bounds truncation round-off by $2^{-\text{fractionalBits}}$ (`L211`, full 1-ULP directed truncation rather than $0.5\text{ ULP}$). If `maxAbs(I)` exceeds `[-2^(bitlength-1), 2^(bitlength-1) - 1]`, `absRoundoff` throws `OverflowException` (`L19-21`), pruning infeasible assignments during `MixedPrecisionOptimizationPhase`.
   - **Host-Double ULP Conversion Detail (`FinitePrecision.scala:142-143, 159-160`):** For `Float32` and `Float64`, `_absRoundoff(i)` computes `Rational.fromDouble(math.ulp(Math.nextUp(Interval.maxAbs(i).doubleValue))) / Rational(2)` instead of `machineEpsilon * maxAbs(i)`. Using `Math.nextUp(...)` ensures that exact powers of two $2^k$ step into the upper binade $(2^k, 2^{k+1})$ with spacing $2^{k-52}$ (preventing an unsound $2\times$ underestimate if an interval approaches $2^k$ from above and `.doubleValue` rounds down to $2^k$), while also giving `[0, 0]` a non-zero floor of $2^{-1075}$ (`ulp(nextUp(0.0))/2`).

---

### 4. Subnormal Underflow (`FTZ`/`DAZ`), Sterbenz Exactness, and FMA Contraction Hazards

`Basis: normative + source + execution`

#### 4.1 Subnormal Relative-Error Blowup vs. `FTZ`/`DAZ` Hardware Unsoundness

In IEEE 754 `binary64`, normal floats $2^{-1022} \le |x| \le (2 - 2^{-52})2^{1023}$ maintain 53 bits of significand precision ($|\text{RN}(x) - x| / |x| \le 2^{-53}$). Below $2^{-1022}$, subnormals $k \cdot 2^{-1074}$ ($1 \le |k| \le 2^{52}-1$) fix absolute spacing at $2^{-1074}$ while significand bits shrink from 52 down to 1:
- **Pure-Relative $(1+\epsilon)$ Model Failure:** At $x_{\text{tiny}} = 3 \cdot 2^{-1074}$, IEEE 754 `RN(x_tiny * 0.5)` rounds tie-to-even from $1.5 \cdot 2^{-1074}$ to $2 \cdot 2^{-1074}$. Exact absolute error is $2^{-1075}$ ($\le \delta_{64}$), but **exact relative error is $\frac{1}{3} \approx 0.333333$**—exceeding $u = 2^{-53} \approx 1.11 \times 10^{-16}$ by **$3.0 \times 10^{15}\times$**! Any verification pass that drops $\delta_i$ (`--denormals=false` without proving $|v(x)| \ge 2^{-1022}$ at every intermediate node) is unsound whenever subnormals are reachable.
- **Hardware `FTZ` / `DAZ` Invalidation of Hauser's Theorem (`FPTaylor` & `Daisy`):** When x86 SSE/AVX `MXCSR` sets `FTZ` (bit 15, flushing subnormal results to $\pm 0$) or `DAZ` (bit 6, treating subnormal inputs as $\pm 0$), or on ARM `FPCR.FZ = 1` / GPU fast-math modes:
  1. Worst-case absolute rounding error on $[ -2^{-1022}, 2^{-1022} ]$ jumps from $2^{-1075}$ to **$2^{-1022}$** ($2^{53}\times$ larger, invalidating `Daisy`'s `Float64.denormalsError = 2^-1075`).
  2. Hauser's theorem breaks: for normal floats $a = 1.5 \cdot 2^{-1022}$ and $b = 1.0 \cdot 2^{-1022}$, IEEE gradual underflow computes $a - b = 2^{-1023}$ *exactly* ($\text{err} = 0$), whereas `FTZ` flushes $a - b$ to `+0.0` ($\text{err} = 2^{-1023}$), **invalidating `FPTaylor`'s unconditional `delta_exp = 0` rewrite on `Op_add`/`Op_sub` (`rounding_simpl.ml:114-120`)**!

#### 4.2 Sterbenz Cancellation (`sub2`) and FMA Contraction Asymmetry

- **Sterbenz's Lemma (`formal/rounding.hl:54-65`, `taylor_form.ml:351-370`):** If $x, y \in \mathbb{F}$ are finite floating-point numbers satisfying $\frac{y}{2} \le x \le 2y$, then $x - y$ is **exact** in IEEE 754 gradual-underflow arithmetic ($\epsilon_{\text{sub}} = 0, \delta_{\text{sub}} = 0$). `FPTaylor` encodes this via piecewise operator `sub2(x, y) = if (x/2 <= y /\ y <= 2*x) then 0 else x - y` (`rounding.hl:54-55`) inside `rounded_sub_form` (`taylor_form.ml:358`).
- **FMA Single Rounding vs. Contraction Asymmetry (`taylor_form.ml:756-761`):** Hardware `fma(a, b, c) = RN(a * b + c)` eliminates the intermediate multiplication rounding variable $\epsilon_{\text{mul}}$, which `FPTaylor` models by lowering `Op_fma(a, b, c)` to exact `add_form cs (mul_form cs a b) c` inside a single outer `Rounding` node (`L714-716, 760`). However, two subtle hazards govern FMA transformations:
  1. **Compiler Contraction (`-ffp-contract=fast`) Breaks Non-Negativity of $x^2 - y^2$:** In uncontracted IEEE 754, $\text{RN}(x \cdot x) - \text{RN}(y \cdot y) = 0$ identically whenever $x = \pm y$. When a compiler contracts only one product into `fma(x, x, -RN(y * y))`, any float $x$ whose square rounds *up* ($\text{RN}(x^2) > x^2$) yields $x^2 - \text{RN}(x^2) < 0$. Specifically, at $x = y = 1 + 5 \cdot 2^{-28}$, $x^2 = 1 + 5\cdot 2^{-27} + 25\cdot 2^{-56}$; since $25\cdot 2^{-56} = 1.5625 \cdot 2^{-52}$ rounds up to $2 \cdot 2^{-52}$, $\text{fma}(x, x, -\text{RN}(y^2)) = -7 \cdot 2^{-56} = -9.7144514654701197 \times 10^{-17} < 0$, causing **`sqrt(x*x - y*y)` to return `-nan` (`isnan == 1`)** (Executable Probe 2)!
  2. **Double Rounding When Emulating Lower Precision:** Computing `fma` in `binary64` and casting to `binary32` is *not* equivalent to `binary32` `fmaf` when $a \cdot b + c$ lands on a `binary32` midpoint after rounding to `binary64`.

---

### 5. Machine-Checked Certificate Pipelines: HOL Light, Gappa, and Lean 4 (`LeanCert`)

`Basis: normative + source`

| Tool / Framework | Primary Analysis Calculus | Transcendentals | Subnormal / FMA Handling | Machine-Checked Proof Export & TCB Boundary |
| :--- | :--- | :--- | :--- | :--- |
| **`Herbie`** (`4612b0d4...`) | `rival` MPFR sampling + `egg` e-graphs + series + DP regimes | Full `libm` / MPFR | Models target `platform` empirically; can introduce overflow/`-0.0`/jump traps | **None** (heuristic synthesis oracle; requires downstream verifier) |
| **`FPTaylor`** (`b5a77cae...`) | Bottom-up 1st-order Symbolic Taylor + global B&B (`opt_basic_bb`, `gelpia`, `z3`) | Rigorous 2nd-order `uop_form` enclosures | Default `delta_exp = e_min` (`-1022`), `delta=0` on `+/-`/`sqrt`; exact `Op_fma` | **HOL Light** (`formal/`), **except** unsupported under `fp-power2-model=true` or `develop=true` (`fptaylor.ml:649-661`) |
| **`Daisy`** (`6a6f47ab...`) | Forward Interval/Affine + subdivision + symbolic Hessian Taylor | Interval / `dReal` / `Metalibm` | `DenormalCheck` (`2^-1075` in `Float64`), `FixedPrecision`, `ap_fixed` | Scala/C/HLS codegen; optional Coq script emission for restricted arithmetic subsets |
| **`Gappa`** (`TOMS 2010`) | Interval + forward relative/absolute error rewrite saturation + bisection | External polynomial approximations only | Exact fixed-point & IEEE subnormal/FMA rounding predicates | **Coq (`Flocq`)** and **HOL Light** proof terms |
| **`LeanCert`** (`44b323a0...`) | Rational/dyadic/affine/Taylor/Bernstein intervals + B&B optimization in Lean 4 | Verified Taylor/Chebyshev enclosures | Models $\mathbb{R}$/dyadic bounds; composes with IEEE specs (`FloatSpec`) | **Lean 4 Kernel** *only* when `leancert.trust = "kernel"` (`default = "native"` uses `Lean.ofReduceBool`) |

#### 5.1 Certificate Restrictions in `FPTaylor` (`fptaylor.ml:649-661`) and `Gappa`

- **`FPTaylor` HOL Light Proof Gate:** Inspecting `validate_proof_record` (`fptaylor.ml:649-661`) shows that setting `proof-record = true` emits explicit warnings that formal proof certificates are **not implemented** for `fp-power2-model = true` (which enables `p2max` binade tightening and `precise_const_rnd_form`) or `develop = true` (which gates `rounded_sub_form`'s Sterbenz `sub2` cancellation at `taylor_form.ml:704-713`). Furthermore, `formal/ieee754/README.md:7-8` notes that `FPTaylor`'s active HOL Light certificate checker verifies bounds relative to the abstract real rounding axioms `is_rnd(c, e2, d2)` rather than linking bit-level IEEE 754 hardware encodings end-to-end.
- **`Gappa` (`DOI: 10.1145/1644001.1644002`):** Excels at low-level polynomial approximations (`libm` Cody–Waite range reduction, double-word Dekker/Knuth `Fast2Sum`/`TwoProd`, FMA residuals) where human or tool-supplied algebraic hints (`e_fp - e_real -> (e_fp - poly) + (poly - e_real)`) split rounding error from truncation error, exporting complete `Flocq` Coq theorems down to bit-level IEEE 754 formats.

#### 5.2 TCB Isolation in Lean 4 Numerical Certificates (`alerad/leancert`)

`LeanCert` bridges computational interval/dyadic/affine optimization into Lean 4 `ℝ` inequalities through golden rational endpoint theorems (`LeanCert/Cert/Interval.lean:35-62`, `verify_rat_upper`, `verify_rat_lower`) paired with `closeBridgeWithVerificationTypedImpl` (`LeanCert/Tactic/BridgeNative.lean:49-80`).

Direct inspection of `LeanCert/Tactic/Verification.lean:18-110` reveals a critical **Trusted Computing Base (TCB) hazard** for strict formal verification pipelines:
- **Default Mode Is `.native` (`L51-57`):** `register_option leancert.trust` defaults to `"native"`, closing boolean certificate goals via `nativeEqTrue` (`native_decide`), which injects the auxiliary axiom **`Lean.ofReduceBool`** into `#print axioms`—adding the entire Lean-to-C compiler, LLVM/C toolchain, and runtime evaluators to the TCB.
- **`.auto` Mode Silently Escalates TCB on Large Certificates (`L59-92`):** Even under `leancert.trust = "auto"`, cost gates (`leancert.trust.autoGate := true`) bypass pure kernel reduction and jump straight to `native_decide` whenever finite sums exceed `autoMaxSumTerms = 2000` (`L74`), integration partitions exceed `autoMaxPartitions = 500` (`L81`), branch-and-bound iterations exceed `autoMaxOptIterations = 100` (`L87`), or elaboration exceeds `kernelHeartbeats = 400000` (`L59`), logging only once per process (`autoFallbackReported`, `L102`).
- **Mandatory Invariant for Zero-`ofReduceBool` Verification:** Any Lean 4 repository enforcing kernel-only axiom audits (forbidding `sorryAx` and `Lean.ofReduceBool`) **must** configure `set_option leancert.trust "kernel"` (or pass per-tactic `(trust := kernel)`), which invokes `decide +kernel` (`mkAuxLemma`) and fails closed (`L26-27`) rather than falling back to native evaluation.

## Boundaries

- **Data-Dependent Loops and Unbounded Iterative Convergence (`unsupported`):** `FPTaylor` analyzes straight-line / `let`-DAG numerical expressions only (`unsupported` for loops). `Daisy` unrolls bounded loops statically or requires manual loop invariants; unbounded iterative linear/nonlinear solvers (CG, Newton, EKF) are unsupported without external Lyapunov/contraction proofs.
- **Exception-Flag (`FE_INEXACT`, `FE_UNDERFLOW`, `FE_INVALID`) and NaN-Payload Preservation (`known not to apply`):** Neither `Herbie` rewrites nor `FPTaylor`/`Daisy` real-error enclosures preserve IEEE 754 sticky status flags or NaN payload bits; algebraic rewrites routinely introduce or eliminate `FE_INEXACT` and `FE_OVERFLOW` side effects.
- **Certified End-to-End Correctness of `Herbie` Outputs (`known not to apply`):** `Herbie` (`4612b0d493cbb2013dc5afac5c099b7722166ec2`) includes internal rule-soundness sanity checks (`prove-rules.rkt` / `test-rules.rkt` over $\mathbb{R}$), but its synthesized floating-point programs carry **no sound worst-case error guarantee** over un-sampled inputs without re-verifying every conditional regime branch in `FPTaylor`, `Daisy`, `Gappa`, or `LeanCert`.
- **Hardware `libm` Transcendental Faithfulness Assumptions (`unknown`):** `FPTaylor` (`rnd64(sin(x))` with `c = 1.0` or `2.0`) and `Daisy` (`_absTranscendentalRoundoff = 2 * _absRoundoff`, i.e., `1.0 ULP` at `FinitePrecision.scala:55`) assume the target runtime `libm` satisfies 0.5-ULP (`CR-libm` / `CORE-MATH`) or 1.0-ULP bounds; whether an unverified system `libm` (such as glibc on extended inputs or GPU `__sinf` intrinsics) meets that bound is unknown to the static analyzer unless explicitly parameterized via `rnd[64, ne, c, ...]`.
- **Stochastic Rounding and FP8 Tensor-Core Accumulation Trees (`not examined`):** While `Daisy` defines a scalar `Float8` `(4, 3)` precision (`FinitePrecision.scala:101-112`), hardware stochastic rounding modes and mixed-precision FP8/BF16 block-scaled matrix-multiply (`MXFP8`) accumulation trees were not examined.

## Evidence

### Primary Repositories and Source Coordinates

1. **`herbie-fp/herbie`** (`revision: 4612b0d493cbb2013dc5afac5c099b7722166ec2`):
   - `src/core/localize.rkt:57-65, 125-215`: `eval-progs-real`, `remove-infinities`, `compute-errors`, and single-operation `local-error` attribution in bits.
   - `src/core/regimes.rkt:34-57, 120-260`: `pareto-regimes`, `branch-vs`, and dynamic-programming `infer-option` split-point synthesis.
   - `src/core/egg-herbie.rkt`, `src/core/egglog-herbie.rkt`, `src/core/taylor.rkt`, and `src/platforms/rival.rkt`: e-graph equality saturation, symbolic series expansion, and MPFR interval real oracle.
2. **`soarlab/FPTaylor`** (`revision: b5a77cae348400f21f83512210d9f43c4bffb381`):
   - `rounding.ml:56-163`: `eps_delta_from_bits` (`float64 -> (-53, -1022)`), directed-rounding `2.0 *. c` multiplier (`L101`), `create_explicit_rounding`, and `get_eps` (`-1074` OCaml float floor at `L163`).
   - `rounding_simpl.ml:102-144`: `simplify_rounding` setting `delta_exp = 0` on `Op_add`/`Op_sub` (`special_flag = true`) and `Op_sqrt`, and `eps_exp = 0` on power-of-two scalings.
   - `taylor_form.ml:19-30, 110-135, 297-765`: `taylor_form` (`v0`, `v1`), shared-index `merge`, `rounded_sub_form` (`mk_floor_sub2`), `mul_form`, `uop_form` 2nd-order remainders, `abs_form`/`max_form`/`min_form`, and `Op_fma` (`L760`).
   - `fptaylor.ml:280-440, 649-661`: `opt-approx` vs. `opt-exact` global error objectives and `validate_proof_record` HOL Light restrictions.
   - `formal/rounding.hl:27-66` and `formal/build_tform2.hl:48-76`: HOL Light `p2max`, `is_rnd_gen`, `sub2` Sterbenz lemmas, and `rnd64` (`ipow2 (-- &53), ipow2 (-- &1022)`).
3. **`malyzajko/daisy`** (`revision: 6a6f47abdd231d3009444e9e1b8ce9febc28c27e`):
   - `src/main/scala/daisy/tools/FinitePrecision.scala:10-224`: `DenormalCheck` (`Float16` $2^{-25}$, `Float32` $2^{-150}$, `Float64` $2^{-1075}$), `Math.nextUp` ULP computation (`L143, 160`), and signed two's-complement `FixedPrecision` bit allocation (`L192-223`).
   - `src/main/scala/daisy/analysis/TaylorErrorPhase.scala:64-110` and `tools/Taylor.scala:56-148`: `epsilonDeltaAbstract`, symbolic `getDerivative`, and quadratic `getTaylorRemainder`.
   - `src/main/scala/daisy/lang/Types.scala:55-59`: `FinitePrecisionType` and Vivado HLS `APFixedType`.
4. **`FPBench/FPBench`** (`revision: 090d81982edc0d2a597f4c15644253d4f266a6ef`): standard `FPCore` benchmark suite and precision/rounding metadata definitions.
5. **`alerad/leancert`** (`revision: 44b323a0d6af00211d5013f6e021432db032087c`):
   - `LeanCert/Cert/Interval.lean:35-62`: `verify_rat_upper` and `verify_rat_lower` golden rational bridge theorems.
   - `LeanCert/Tactic/BridgeNative.lean:49-80` and `LeanCert/Tactic/Verification.lean:18-110`: `VerificationMode` (`.native`, `.kernel`, `.auto`), default `leancert.trust := "native"`, and calibrated `.auto` fallback thresholds (`autoMaxSumTerms = 2000`, `autoMaxPartitions = 500`, `autoMaxOptIterations = 100`).

### Peer-Reviewed Specifications and Papers

- Marc Daumas and Guillaume Melquiond, *"Certification of Bounds on Expressions Involving Rounded Operators"*, ACM Transactions on Mathematical Software (TOMS) 37(1), Article 3, 2010 (`DOI: 10.1145/1644001.1644002`).
- Pavel Panchekha, Alex Sanchez-Stern, James R. Wilcox, and Zachary Tatlock, *"Automatically Improving Accuracy for Floating Point Expressions"*, PLDI 2015, pp. 1–11 (`DOI: 10.1145/2737924.2737959`).
- Eva Darulova, Anastasiia Izycheva, Fariha Nasir, Fabian Ritter, Heiko Becker, and Robert Bastian, *"Daisy – Framework for Analysis and Optimization of Numerical Programs (Tool Paper)"*, TACAS 2018, LNCS 10805, pp. 270–287 (`DOI: 10.1007/978-3-319-89960-2_15`).
- Alexey Solovyev, Marek S. Baranowski, Ian Briggs, Charles Jacobsen, Zvonimir Rakamarić, and Ganesh Gopalakrishnan, *"Rigorous Estimation of Floating-Point Round-Off Errors with Symbolic Taylor Expansions"*, ACM TOPLAS 41(1), Article 2, 2018 (`DOI: 10.1145/3230733`).
- Max Willsey, Chandrakana Nandi, Yisu Remy Wang, Oliver Flatt, Zachary Tatlock, and Pavel Panchekha, *"egg: Fast and Extensible Equality Saturation"*, PACMPL 5(POPL), Article 23, 2021 (`DOI: 10.1145/3434304`).
- IEEE Computer Society, *"IEEE Standard for Floating-Point Arithmetic"*, IEEE Std 754-2019.

### Executable Probe 1: Herbie Cancellation vs. Intermediate Overflow, `-0.0` Polarity Flip, and Regime-Split Non-Monotonicity

Executed on Linux (`Python 3.13`, standard library `math` and `struct` only; observed `2026-11-19`):

```bash
python3 - <<'EOF'
import math, struct

def f64_bits(x: float) -> int:
    u = struct.unpack(">Q", struct.pack(">d", x))[0]
    return (1 << 64) - u if (u >> 63) else u + (1 << 63)

def herbie_bits_error(actual: float, exact_float: float) -> float:
    if math.isnan(actual) or math.isnan(exact_float) or (math.isinf(actual) and not math.isinf(exact_float)):
        return 64.0
    return math.log2(1.0 + abs(f64_bits(actual) - f64_bits(exact_float)))

for x, exact_ref in [(1e8, 0.5e-8 - 0.125e-24), (1e160, 0.5e-160)]:
    naive = math.sqrt(x * x + 1.0) - x
    rationalized = 1.0 / (math.sqrt(x * x + 1.0) + x)
    spliced = (0.5 / x) if x > (2.0 ** 27) else (1.0 / (math.sqrt(x * x + 1.0) + x))
    print(f"x={x:.0e}: naive={naive!r} ({herbie_bits_error(naive, exact_ref):.1f}b err), "
          f"rat={rationalized!r} ({herbie_bits_error(rationalized, exact_ref):.1f}b err), "
          f"spliced={spliced!r} ({herbie_bits_error(spliced, exact_ref):.1f}b err)")

z_neg = -0.0
e_naive = math.exp(z_neg) - 1.0
e_expm1 = math.expm1(z_neg)
print(f"signed_zero: exp(-0.0)-1 = {math.copysign(1.0, e_naive):+.0f}*0.0 (1/f={math.copysign(float('inf'), e_naive)}), "
      f"expm1(-0.0) = {math.copysign(1.0, e_expm1):+.0f}*0.0 (1/f={math.copysign(float('inf'), e_expm1)})")

s = 1e-5
s_prev = math.nextafter(s, -math.inf)
p3_prev = s_prev * (1.0 + s_prev * (0.5 + s_prev / 6.0))
naive_curr = math.exp(s) - 1.0
print(f"regime_monotonicity at split s={s}: s_prev < s ({s_prev < s}), "
      f"P3(s_prev)={p3_prev:.17e}, exp(s)-1={naive_curr:.17e}, "
      f"monotone={p3_prev <= naive_curr}, jump={naive_curr - p3_prev:.3e}")
EOF
```

Recorded output:

```text
x=1e+08: naive=0.0 (62.0b err), rat=5e-09 (0.0b err), spliced=5e-09 (0.0b err)
x=1e+160: naive=inf (64.0b err), rat=0.0 (60.9b err), spliced=5e-161 (0.0b err)
signed_zero: exp(-0.0)-1 = +1*0.0 (1/f=inf), expm1(-0.0) = -1*0.0 (1/f=-inf)
regime_monotonicity at split s=1e-05: s_prev < s (True), P3(s_prev)=1.00000500001666665e-05, exp(s)-1=1.00000500000696491e-05, monotone=False, jump=-9.702e-17
```

### Executable Probe 2: Symbolic Taylor vs. Naive Interval Tightening, Exact Subnormal Relative Blowup, and FMA `sqrt(x^2 - y^2)` `NaN` Witness

Executed with `Python 3.13` (`fractions`) and `gcc -O2 -lm` on Linux x86_64 (`observed_at: 2026-11-19`):

```bash
python3 - <<'EOF'
from fractions import Fraction
import math, subprocess

u = Fraction(1, 1 << 53)
naive_forward_iv_bound = Fraction(5, 2) * u
m2 = Fraction(2, 3) * (Fraction(1, 1) / (1 - u)**3 + Fraction(1, 1) / (1 - u)**2) * (u ** 2)
sym_taylor_bound = Fraction(4, 3) * u + m2

max_emp = max(
    abs(Fraction((1.0 + k / 200000.0) / ((1.0 + k / 200000.0) + 1.0))
        - Fraction(1.0 + k / 200000.0) / (Fraction(1.0 + k / 200000.0) + 1))
    for k in range(200001)
)
print(f"x/(x+1) bounds (u=2^-53): empirical_max={float(max_emp/u):.6f}u, "
      f"symbolic_taylor={float(sym_taylor_bound/u):.6f}u, naive_interval={float(naive_forward_iv_bound/u):.6f}u, "
      f"tightening_ratio={float(naive_forward_iv_bound/sym_taylor_bound):.4f}x")

x_tiny = 3.0 * math.ldexp(1.0, -1074)
fl_half = x_tiny * 0.5
exact_half = Fraction(x_tiny) * Fraction(1, 2)
abs_err = abs(Fraction(fl_half) - exact_half)
rel_err = abs_err / exact_half
print(f"subnormal exact: abs_err_eq_2^-1075={abs_err == Fraction(1, 1 << 1075)}, "
      f"float_underflows_abs_err={float(abs_err) == 0.0}, rel_err={rel_err} ({float(rel_err):.6f})")

c_src = r"""
#include <stdio.h>
#include <math.h>
int main(void) {
    volatile double x = 1.0 + 5.0 * ldexp(1.0, -28);
    volatile double y = x;
    double uncontracted = x * x - y * y;
    double contracted = fma(x, x, -(y * y));
    printf("x=%.17g: uncontracted=%.17g sqrt=%g | fma_contracted=%.17g sqrt=%g (isnan=%d)\n",
           x, uncontracted, sqrt(uncontracted), contracted, sqrt(contracted), isnan(sqrt(contracted)));
    return 0;
}
"""
with open("/tmp/fma_nan_probe.c", "w") as f:
    f.write(c_src)
subprocess.check_call(["gcc", "-O2", "/tmp/fma_nan_probe.c", "-lm", "-o", "/tmp/fma_nan_probe"])
print(subprocess.check_output(["/tmp/fma_nan_probe"]).decode().strip())
EOF
```

Recorded output:

```text
x/(x+1) bounds (u=2^-53): empirical_max=0.999590u, symbolic_taylor=1.333333u, naive_interval=2.500000u, tightening_ratio=1.8750x
subnormal exact: abs_err_eq_2^-1075=True, float_underflows_abs_err=True, rel_err=1/3 (0.333333)
x=1.0000000186264515: uncontracted=0 sqrt=0 | fma_contracted=-9.7144514654701197e-17 sqrt=-nan (isnan=1)
```

## Revalidation

To cheaply revalidate these findings against newer upstream commits of `Herbie`, `FPTaylor`, `Daisy`, or `LeanCert`:

1. **`FPTaylor` Subnormal & Proof-Certificate Gates:** Diff `rounding.ml` (`eps_delta_from_bits`, `get_eps`), `rounding_simpl.ml` (`simplify_rounding`), `formal/build_tform2.hl` (`rnd64`), and `fptaylor.ml` (`validate_proof_record`) to check whether default `rnd64` `delta_exp` remains `-1022`, whether `Op_add`/`Op_sub` still force `delta_exp = 0`, and whether `fp-power2-model` / `develop` have gained HOL Light proof support.
2. **`Daisy` Precision & Taylor Engines:** Diff `src/main/scala/daisy/tools/FinitePrecision.scala` (`DenormalCheck`, `FixedPrecision`, `_absRoundoff`) and `analysis/TaylorErrorPhase.scala` to verify `denormalsError` exponents and `Math.nextUp` ULP handling.
3. **`LeanCert` Kernel Trust Boundary:** Diff `LeanCert/Tactic/Verification.lean` around `register_option leancert.trust` (`defValue`) and `VerificationMode` to confirm whether `"native"` (`Lean.ofReduceBool`) remains the default and whether `"kernel"` still enforces zero-fallback `decide +kernel`.
4. **IEEE 754 Rewrite & FMA Counterexamples:** Rerun Executable Probes 1 and 2 (< 1.5 seconds total) on the target CPU/compiler flags to check FMA contraction (`-ffp-contract=off` vs. `fast`) and subnormal (`MXCSR`/`FPCR`) runtime behavior.
