# Prospective sizing for paired binary checker evaluations, covering-array design/held-out splits, and benchmark governance (McNemar, TOST, Neyman, IPOG/PICT, SMT-COMP, sv-benchmarks)

## Summary

- **Paired sizing depends on discordance, not on the marginals.** Let δ = p10 − p01 (effect) and ψ = p10 + p01 (discordance) for two checkers run on the same instances. Connor's form gives n = (z₁₋α/₂√ψ + z₁₋β√(ψ − δ²))²/δ². With marginals held at 0.80 versus 0.70, the 80%-power n still ranges from 108 pairs (ψ = 0.14) to 391 pairs (ψ = 0.50). *Basis: derived + execution.*
- **The pre-registered test changes n.** The exact conditional McNemar test has true size 0.005–0.035 at nominal 0.05. At 80% power it needs 3–9% more pairs than Connor (between −2% and +5% at 90%). Mid-p and the asymptotic test never need more than Connor's n. This agrees with Fagerland et al. (2013). Pairing alone cuts 588 unpaired instances to 296 (φ = 0) or 124 (φ = 0.6). *Basis: execution + documentation.*
- **TOSTER (pin `9ea2bf2`) sizes only unpaired two-proportion TOST.** Paired equivalence with true δ = 0 needs n = (z₁₋α + z₁₋β/₂)²ψ/Δ². At Δ = ψ = 0.10 that is 86 paired instances. TOSTER's unpaired formula at pA = pB = 0.80 gives 550. Exact Wald paired-TOST power is saw-toothed in n, and its size at the margin is 0.055. *Basis: source + derived + execution.*
- **Precision floors dominate.** A ±0.10 interval needs 78–104 observations and ±0.05 needs 320–402. A result of 3/10 has the Clopper–Pearson interval [0.067, 0.652], which no plausible outcome can falsify. Neyman allocation gains only about 9% here; per-stratum floors and Bonferroni α/k set the total. *Basis: execution.*
- **Covering-array splits.** PICT (pin `ab76c25`) arrays are complete and constraint-respecting; NIST CCMCL agrees in 8 of 8 cases. Randomly halving one array loses 38–43% of valid t-tuples per side, and 0 of 10,000 splits left both halves complete. Three constructions guarantee both sides:
  - a `Split` factor outside a sub-model (2× rows);
  - two arrays generated with different `/r:N` (≈2× rows, with novel (t+1)-tuples on the held-out side);
  - `Split` at strength t+1 (≈4–5× rows).

  Filtering an unconstrained array afterwards loses 15–23% of valid tuples. *Basis: execution + source.*
- **Governance.** SMT-COMP uses per-logic caps, removes trivially solved benchmarks, draws its random value from inputs no single party controls, scrambles benchmarks, and recuses affiliated organizers. sv-benchmarks uses pull-request review, license and provenance rules, `expected_verdict` YAML files and `c/check.py`. Neither project's examined rules or code describe a blinded held-out set. SMT-COMP's code departs from its rules on how new benchmarks are prioritized. *Basis: normative + source.*

## Applicability

Scope: planning, before any data exist, of evaluations with one binary outcome per instance (checker accept/reject, verdict correct/incorrect, obligation discharged or not). The corpus is finite and stratified by factors such as construct, rule, fault mode and context, and it is split into a design side and a held-out side.

The formulas assume independent instances or pairs. Variants of one generator template are clustered; they need a design-effect inflation, which is not derived here.

Post-hoc zero-numerator intervals and adaptive reuse of a holdout are covered by the related package `reusable-holdout-thresholdout-ladder-leaderboards-and-clopper-pearson-zero-numerators`.

| Subject | Pin | Role |
|---|---|---|
| `Lakens/TOSTER` 0.9.0 | `9ea2bf25e1a98ce0713f9aa16294872cb26b75a8` | source read; formulas transcribed to Python (no R runtime available) |
| `microsoft/pict` | `ab76c2548f551fcb46314e58653a1bd1172f3a72` | built and executed; all covering-array behavior reported here comes from this build |
| `usnistgov/combinatorial-testing-tools` (archived) | `e4df6c47e251800533610c48446460075fd52e3d` | `ccmcl.jar` used as an independent coverage oracle; ACTS is absent |
| `SMT-COMP/smt-comp` | `68a5cdc72f8f5e2eb348bdfe7ab4d83842d3b54f` | 2025 rules (normative) |
| `SMT-COMP/smt-comp.github.io` | `cd15cbedd4ef312d615448100797a80e922cf575` | 2026 selection code and `web/static/rules.pdf`; code findings hold for `Config.current_year = 2026` |
| `sosy-lab/sv-benchmarks` (archived mirror, last commit 2021-10-03; the project moved to GitLab) | `2e1723fde6aa65a250dcb677efa45edaa4b6b631` | governance as of that snapshot only |

Host: x86_64 Linux, Xeon 2.6 GHz, 96 logical CPUs, g++ 15.2, Python 3.13 (stdlib only), OpenJDK 27 under Xvfb. Timings under about 10 ms are mostly process start-up.

What generalizes:
- The statistics are host-independent.
- The PICT numbers come from one 7×5×5×4 model and one 5¹⁰ model.
- Split-loss magnitudes depend on how redundant an array is. Only their sign follows from the counting argument in §8.

## Findings

### 1. Notation and the unifying abstraction (C2)

Notation: p11, p10, p01, p00 are the joint pass/fail probabilities of checkers (A, B) on one instance. pA = p11 + p10. δ = pA − pB = p10 − p01. ψ = p10 + p01. φ is the within-pair correlation, so p11 = pA·pB + φ√(pA·qA·pB·qB). Δ is the equivalence or non-inferiority margin (the smallest effect size of interest).

Every design here reduces to choosing n_h per stratum so that a pre-registered estimator achieves one of: a stated half-width; power against a null (superiority); or power against both one-sided nulls (TOST). A covering array is a stratification constraint: every valid t-tuple must have n_h ≥ 1 on each side. The statistics then raise that floor of 1. *Basis: derived.*

### 2. Paired superiority: McNemar family and Connor's n

**Formula.**

```text
n_pairs = ( z_{1-α/2}·sqrt(ψ) + z_{1-β}·sqrt(ψ − δ²) )² / δ²
```

Derivation: D = n10 − n01 has mean nδ and variance n(ψ − δ²). Reject when |D| > z√(nψ); set the power to 1 − β and solve for n. Because ψ is also used under the null, the formula is conservative against the asymptotic test. Attribution to Connor (1987) was verified only through search metadata; the JSTOR page was behind an automated challenge. *Basis: derived + documentation (secondary).*

**Exact power** (`support/stats_probes.py` §A). Enumerate m = n10 + n01 ~ Bin(n, ψ) and n10 | m ~ Bin(m, p10/ψ). The test definitions follow Fagerland et al. (2013), eqs. (1)–(5):
- exact conditional: two-sided p = 2·P(X ≤ min), X ~ Bin(m, ½);
- mid-p: that p minus f(n12 | m);
- asymptotic: z = (n12 − n21)/√(n12 + n21);
- with continuity correction: z = (|n12 − n21| − 1)/√(n12 + n21).

True size at nominal α = 0.05, with p10 = p01 = 0.10. *Basis: execution.*

| n | exact cond. | mid-p | asymptotic | asymptotic + CC |
|---|---|---|---|---|
| 20 | 0.0048 | 0.0171 | 0.0444 | 0.0048 |
| 50 | 0.0221 | 0.0413 | 0.0429 | 0.0218 |
| 100 | 0.0294 | 0.0457 | 0.0522 | 0.0266 |
| 200 | 0.0346 | 0.0483 | 0.0493 | 0.0332 |

Smallest n reaching 80% or 90% power (power stayed above target for all larger n in each scanned window). *Basis: execution.*

| δ | ψ | Connor 80% | exact / mid-p / asymptotic, 80% | Connor 90% | exact / mid-p / asymptotic, 90% |
|---|---|---|---|---|---|
| 0.10 | 0.12 | 91.8 | 95 / 82 / 79 | 121.9 | 119 / 104 / 103 |
| 0.10 | 0.20 | 154.6 | 168 / 152 / 145 | 206.0 | 215 / 199 / 197 |
| 0.10 | 0.30 | 233.1 | 249 / 230 / 229 | 311.0 | 325 / 308 / 305 |
| 0.10 | 0.40 | 311.6 | 329 / 311 / 311 | 416.1 | 433 / 415 / 415 |
| 0.05 | 0.10 | 311.6 | 337 / 305 / 291 | 416.1 | 431 / 398 / 394 |
| 0.05 | 0.20 | 625.5 | 658 / 622 / 622 | 836.4 | 867 / 830 / 830 |
| 0.20 | 0.30 | 56.4 | 61 / 53 / 53 | 74.6 | 78 / 70 / 68 |

At fixed marginals pA = 0.80 and pB = 0.70 (so δ = 0.10), the Connor 80% n is 107.5, 154.6, 233.1, 311.6 and 390.1 for ψ = 0.14, 0.20, 0.30, 0.40 and 0.50. The feasible range is 0.10 ≤ ψ ≤ 0.50. *Basis: execution.*

Sizing with Connor's n and then analysing with the exact conditional test under-powers the study (all 7 rows at 80%, 6 of 7 at 90%). Either pre-register mid-p or the asymptotic test, or size by enumerating the test you will actually run. Estimate ψ from pilot pairs on design-side instances, or bracket it.

Fagerland et al. report that the mid-p test "did not violate the nominal level in any of the 9595 scenarios", that the largest asymptotic-test size they observed was 5.37%, and: "We do not recommend use of the McNemar exact conditional test nor the asymptotic test with CC in any situation." *Basis: documentation (full text read).*

### 3. Unpaired versus paired

Fleiss's unpaired formula without continuity correction:

```text
n = ( z_{1-α/2}·sqrt(2·p̄·q̄) + z_{1-β}·sqrt(pA·qA + pB·qB) )² / δ²
```

For pA = 0.80 and pB = 0.70 this gives 293.2 per group, i.e. 588 instances. The paired equivalents are below (φ ≤ 0.7638 is feasible). *Basis: derived + execution.*

| φ | ψ | Connor n (instances / runs) | exact-conditional n80 |
|---|---|---|---|
| 0.0 | 0.3800 | 296 / 592 | 313 |
| 0.2 | 0.3067 | 239 / 478 | 255 |
| 0.4 | 0.2334 | 181 / 362 | 193 |
| 0.6 | 0.1600 | 124 / 248 | 132 |

### 4. Precision sizing and falsifiability bands (V1)

n for a 95% half-width h. Wilson and Clopper–Pearson use the smallest n whose interval at x = round(p·n) has half-width ≤ h. *Basis: execution.*

| p | h | Wald | Wilson | Clopper–Pearson |
|---|---|---|---|---|
| 0.3 | 0.05 | 323 | 320 | 341 |
| 0.3 | 0.10 | 81 | 78 | 88 |
| 0.5 | 0.05 | 385 | 381 | 402 |
| 0.5 | 0.10 | 97 | 93 | 104 |
| 0.9 | 0.10 | 35 | 34 | 42 |

95% Clopper–Pearson intervals:

| x/n | interval | width |
|---|---|---|
| 3/10 | [0.067, 0.652] | 0.586 |
| 12/40 | [0.166, 0.465] | 0.300 |
| 36/120 | [0.220, 0.390] | 0.171 |

**Non-vacuity rule.** A pre-registered band p ∈ [p0 − w, p0 + w] can be falsified only if a realistic alternative p1 produces an interval lying entirely outside the band. This requires the half-width h(n) to be smaller than |p1 − p0| − w. The smallest Clopper–Pearson n at which that happens (*Basis: execution*):

| band | p1 | n |
|---|---|---|
| [0.20, 0.40] | 0.55 | 47 |
| [0.25, 0.35] | 0.45 | 95 |
| [0.75, 0.85] | 0.65 | 79 |

A 95% interval 0.5–0.6 wide is the signature of n ≈ 10.

### 5. Equivalence and non-inferiority (TOST)

**What TOSTER implements** (`R/power_two_proportions.R` at the pin). *Basis: source.*

The deprecated closed form (lines 79–81) is:

```r
NT1<-(prop1*(1-prop1)+prop2*(1-prop2))*((qnorm(1-alpha)+qnorm(1-((1-statistical_power)/2)))/(abs(prop1-prop2)-abs(low_eqbound_prop)))^2
```

It is computed for both bounds and the larger value is taken. This is the unpaired per-group N = (p1q1 + p2q2)(z₁₋α + z₁₋β/₂)²/(|p1 − p2| − Δ)².

`power_twoprop(alternative = "equivalence")` dispatches to `pow_prop_tost`. Its body (lines 236–240) computes `2*(pnorm((abs(p1-p2)-min(null))/sqrt(p1*(1-p1)/n+p2*(1-p2)/n)-qnorm(1-alpha))+…)-1` for each bound, takes the minimum, and inverts it with `uniroot` over [4, 1e7] (line 246).

The roxygen text says "Z-test (pooled)" (line 9), yet the standard error is unpooled. `grep -rni "mcnemar\|discordant\|paired prop" R/` finds nothing. `power_t_TOST(type = "paired")` (`R/power_t_TOST.R` lines 96–99) applies to continuous outcomes only.

**Differential check (V2).** The roxygen examples pair a 90%-power sample-size call (lines 23–30) with a power call at "N 542" (lines 32–39), both at α = 0.05, p1 = p2 = 0.5, Δ = 0.1. The transcription agrees: closed form 541.11, rounded up to 542; uniroot 541.11; power at n = 542 is 0.9006. *Basis: source + execution.*

**Paired-difference TOST** (derived; not a TOSTER function). Conclude equivalence iff δ̂ ± z₁₋α·SE lies within (−Δ, Δ), where δ̂ = (n10 − n01)/n and SE² = (p̂10 + p̂01 − δ̂²)/n. Sample sizes:

```text
true δ = 0:    n = (z_{1-α} + z_{1-β/2})²·ψ/Δ²
true |δ1| > 0: n ≈ (z_{1-α} + z_{1-β})²·(ψ − δ1²)/(Δ − |δ1|)²
non-inferiority (H0: δ ≤ −Δ): n = (z_{1-α} + z_{1-β})²·(ψ − δ1²)/(δ1 + Δ)²
```

Exact power by enumerating the full trinomial (α = 0.05 per one-sided test, 80% target). *Basis: execution.*

| ψ | δ1 | Δ | closed-form n | exact power at ⌈n⌉ | smallest n with exact power ≥ 0.80 |
|---|---|---|---|---|---|
| 0.10 | 0 | 0.10 | 85.6 | 0.8140 | 86 |
| 0.20 | 0 | 0.10 | 171.3 | 0.7966 | 170 |
| 0.10 | 0.02 | 0.10 | 96.2 | 0.7797 | 104 |
| 0.30 | 0 | 0.10 | 256.9 | 0.7985 | 256 |
| 0.20 | 0 | 0.05 | 685.1 | 0.8010 | not scanned |

What the table shows:
- Power is not monotone in n: n = 170 passes 0.80, but n = 172 does not.
- When the true δ is nonzero, the closed form under-sizes.
- The size at the margin (δ = Δ = 0.10, ψ = 0.20) is 0.0562, 0.0548 and 0.0551 at n = 100, 200 and 300, so the test is slightly liberal.
- For pA = pB = 0.80, TOSTER's unpaired formula needs 274.04 per group (550 instances), whereas the paired design needs 85.6.

Lakens (2017) treats the bounds as a smallest effect size of interest that must be justified in advance (bibliographic record only). TOST originates with Schuirmann (1987). *Basis: derived + execution.*

### 6. Stratified allocation, floors, multiplicity

Neyman allocation: n_h = n·W_h·S_h / Σ W_k·S_k with S_h = √(p_h(1 − p_h)), giving Var = (Σ W_h·S_h)²/n (no finite-population correction). Worked example with W = (0.4, 0.3, 0.2, 0.1), p = (0.95, 0.80, 0.50, 0.20) and n = 400 (*Basis: execution*):

| allocation | n_h | Var | 95% half-width |
|---|---|---|---|
| proportional | 160/120/80/40 | 3.325e-4 | 0.0357 |
| Neyman | 100.4/138.3/115.2/46.1 | 3.013e-4 | 0.0340 |
| equal | 100 each | 3.360e-4 | 0.0359 |
| simple random sample | – | 4.810e-4 | 0.0430 |

Stratification saves about 31% of the variance relative to simple random sampling, and Neyman a further 9% over proportional. Per-stratum claims need per-stratum floors: at Wilson h = 0.10 these are 24/60/93/60 (sum 237). Neyman gives the p = 0.20 stratum only 46, below its floor of 60.

Per-stratum n under a Bonferroni-adjusted α/k. *Basis: execution.*

| k | α/k | Wilson n (h = 0.10 / 0.05, p = 0.5) | Connor n80 (δ = 0.10, ψ = 0.20 / δ = 0.20, ψ = 0.30) | paired-TOST n80 (ψ = 0.10, Δ = 0.10) |
|---|---|---|---|---|
| 1 | 0.0500 | 93 / 381 | 154.6 / 56.4 | 85.6 |
| 2 | 0.0250 | 121 / 498 | 187.5 / 68.6 | 105.1 |
| 4 | 0.0125 | 150 / 618 | 220.2 / 80.7 | 124.1 |
| 8 | 0.0063 | 180 / 741 | 252.7 / 92.8 | 142.8 |

For example, 4 strata each with a paired superiority claim at δ = 0.10 need about 4 × 221 = 884 held-out instances. *Basis: derived.*

### 7. Covering-array construction: IPOG versus PICT

**IPOG-Test** (Lei, Kacker, Kuhn, Okun and Lawrence, ECBS 2007, Fig. 2, from the authors' camera-ready copy). *Basis: documentation (paper read).*

```text
ts := one test per value combination of the first t parameters
for i = t+1..n:
  π := all t-way combinations involving P_i and t−1 of P_1..P_{i−1}
  for each τ in ts:   extend τ with the v_i covering most of π; remove covered from π   # horizontal
  for each σ in π:    if covered: drop; else change an existing test's don't-care
                      positions, or add a new test {σ, don't-cares}                    # vertical
```

The paper states: storage for π is O(dᵗ·nᵗ⁻¹); the number of tests is O(dᵗ·log n); time is O(dᵗ⁺¹·nᵗ⁻¹·log n). IPOG-D (STVR 2008, verified bibliographically) adds a recursive construction to cut the number of combinations that must be enumerated.

**PICT is a different algorithm.** `api/model.cpp` lines 85–98 at the pin give the pseudocode for `Model::gcd`:

```text
while (there are still zeros for some combinations) ... while some parameters remain unbound
    is the work list empty? yes: pick a zero from combination with the most zeros, bind corresponding values
                            no:  pull a parameter from the work list and pick a value
```

PICT builds one row at a time (an AETG-style greedy), breaking ties with `GetTask()->Rand()` (lines 301–323). `doc/pict.md` says:
- `/r:N` changes only how combinations are packed into rows and "does not relax the requested coverage target" (lines 94–98);
- removing rows after generation is wrong "because an offending test case may cover other, possibly valid, pairs" (line 104);
- output under `/t:N` is "bit-for-bit identical" whatever the thread count (lines 55–57).

*Basis: source + documentation.*

### 8. Measured: covering arrays and design/held-out splits

**Model** (`support/models/model_constrained.txt`):

```text
Construct: loop, recursion, pointer_arith, array_index, bitfield, union_pun, closure
Rule: bounds, null_deref, int_overflow, uninit_read, alias
Fault: none, off_by_one, missing_guard, wrong_width, use_after_free
Context: straight_line, nested_branch, callee, generic
IF [Fault] = "use_after_free" THEN [Rule] IN {"alias", "null_deref"};
IF [Fault] = "wrong_width" THEN [Rule] IN {"int_overflow", "bounds"};
IF [Construct] = "bitfield" THEN [Fault] <> "use_after_free" AND [Rule] <> "alias";
IF [Construct] = "closure" THEN [Context] <> "straight_line";
IF [Fault] = "off_by_one" THEN [Construct] IN {"loop", "array_index", "pointer_arith", "recursion"};
```

Of the 700 configurations, 442 are valid. A valid t-tuple is a t-projection of a valid full row, found by exact enumeration. PICT `/o:max` emits the same 442 rows as the Python constraint predicate.

PICT supplies the arrays, row counts and timings. Coverage counting, splitting and the IPOG reference are this package's own code. *Basis: execution.*

Coverage (5 runs each). `/t:1` and `/t:auto` outputs are byte-identical; see `support/thread_determinism.txt`. *Basis: execution.*

| t | constrained | rows | required valid t-tuples | covered | invalid rows emitted | wall time |
|---|---|---|---|---|---|---|
| 2 | no | 37 | 163 | 163 | 0 | 2.4–2.6 ms |
| 2 | yes | 39 | 151 | 151 | 0 | 2.6–3.0 ms |
| 3 | no | 180 | 555 | 555 | 0 | 3.5–4.1 ms |
| 3 | yes | 159 | 441 | 441 | 0 | 3.8–4.1 ms |

Split strategies. *Basis: execution.*

| Strategy | Rows at t = 2 (unconstrained / constrained) | Both sides cover all valid t-tuples? | Detail |
|---|---|---|---|
| A. One array, random 50/50 split (10,000 splits, `random.Random(12345)`) | 37 / 39 | **Never.** 0/10,000 at t = 2 and t = 3 | Mean loss per side 0.417 / 0.382 at t = 2 and 0.430 / 0.404 at t = 3. The worse side retains 0.51–0.66. |
| B. `Split: design, heldout` outside sub-model `{Construct, Rule, Fault, Context} @ t`, global `/o:2` | 72 / 72 (t = 3: 370 / 320) | Yes | Every configuration appears on both sides. |
| C. Two arrays with `/r:1,2` and `/r:101,202` | 40+37, 37+37 / 38+38, 39+39 | Yes | Shared identical rows: 1 / 4–5 at t = 2 and 40–46 / 58–63 at t = 3. 94–108 of the held-out side's 143–150 3-tuples are absent from the design side at t = 2. |
| D. `Split` as an ordinary factor at `/o:t+1` | 187 / 165 | Yes | Also covers all 3-tuples overall, by construction of /o:3. |
| E. Generate unconstrained, then delete invalid rows | 24 of 37 kept (t = 2); 113 of 180 kept (t = 3) | – | Loses 35 of 151 valid pairs (23.2%) and 66 of 441 valid triples (15.0%). |

Interpretation (*Basis: derived*):
- **A fails by counting.** A near-minimal array covers many tuples exactly once, and each half loses such a tuple with probability ½. Two complete halves would need covering index λ ≥ 2, i.e. at least twice the t-way lower bound of rows (≥ 70 here).
- **B** is the cheapest guarantee. It tests new instances of configurations already seen.
- **C** additionally tests unseen (t+1)-combinations.
- **E** quantifies PICT's own warning against deleting rows after generation.

Latency for 5¹⁰ (unconstrained, median of 3, `/t:1` / `/t:auto`): t = 2, 47 rows, 0.016 / 0.004 s; t = 3, 310 rows, 0.042 / 0.094 s; t = 4, 1812 rows, 2.056 / 0.880 s. *Basis: execution.*

### 9. Differential validation (V2)

| Check | Result |
|---|---|
| PICT vs. this package's IPOG transcription (unconstrained) | t = 2: 37 vs. 38 rows (lower bound 35). t = 3: 180 vs. 175 (= the bound 7·5·5). Both complete. |
| Own counter vs. NIST CCMCL (`com.nist.ccmcl.Main -A <acts> -T t`) | 8/8 agree to 5 decimals: 1.0 for the full arrays; 0.60123, 0.57297, 0.62914 and 0.60544 for the even-row halves. |
| Own constraint predicate vs. PICT `/o:max` | Identical 442-row set. |
| TOSTER transcription vs. its documented "N 542" | 541.11, which rounds up to 542. |
| Connor vs. exact enumeration | See §2 table. |

ACTS is distributed by e-mail request (`README.md` line 4), so comparing PICT against a second production generator was **not examined**. *Basis: execution.*

### 10. Benchmark governance: SMT-COMP rules versus code

**Rules.** Sources: `rules/rules25.md` in smt-comp, and the 2026 `web/static/rules.pdf` (pp. 12–13). *Basis: normative.*

- **Families.** Families are the submitter's bottom-level directories (rules25.md lines 705–717). Organizers may "cut the size of certain benchmark families to avoid their over-representation" (723–728).
- **Trivial benchmarks.** Single-query selection drops benchmarks "solved by all solvers (including non-competitive solvers) in less than one second" in 2018–2024 (734–736; the 2026 rules keep the same years). Unsat-core selection drops benchmarks with a single `assert`.
- **Cap per logic.** In 2025, min(n, max(300, 50n/100)) (752–763). In 2026:
  - n ≤ 300: all;
  - 300 < n ≤ 600: 300;
  - 600 < n ≤ 1000: 50%;
  - n > 1000: 500 + (n − 1000)/10.

  The 2026 rules draw from the preceding year's SMT-LIB release, citing the 9.98 CPU years SMT-COMP 2025 consumed.
- **New benchmarks.** "first picking randomly one benchmark from each new benchmark family"; the rest are drawn uniformly (765–773).
- **Scrambling and randomness.** Scrambling makes reliance on identifying syntax "cheating" (784–790). Randomness uses C `random()`, initialized via `srandom()` with "the sum, modulo 2³⁰, of the integer numbers provided in the system submissions ... by all SMT-COMP entrants other than the organizers'", plus ⌊100 × the NYSE Composite opening value⌋, so that the organizers cannot steer it (792–804).
- **Recusal.** Organizers affiliated with entrants are recused from decisions (line 1248).

**Code** (`smtcomp/selection.py` and `smtcomp/defs.py` at `cd15cbe`). *Basis: source.*

- **Cap.** `Config` sets `min_used_benchmarks = 300`, `ratio_of_used_benchmarks = 0.5`, `large_logic_threshold = 1000`, `large_logic_used_ratio = 0.1` (defs.py 1466–1469). selection.py lines 134–149 compute sample = min(n, max(300, ⌊n ≤ 1000 ? 0.5n : 500 + 0.1(n − 1000)⌋)), which matches the 2026 rule. Derived examples: n = 450 → 300; 800 → 400; 5000 → 900 (the 2025 rule would give 2500).
- **Triviality.** `find_trivial` (lines 32–72) marks a (file, year) pair trivial when every result is decided with `cpu_time <= 1.0` (line 48). With `old_criteria = False`, a file must be trivial in every year (line 58). Single-query and incremental selection then drop trivial files (lines 110–113).
- **New benchmarks.** `new` means the family name starts with `str(current_year − 1)` (line 92). Lines 150–170 take `new_sample_size = min(sample_size, new_len)` from the new benchmarks and the remainder from old ones, each via Polars `list.sample(n=…)` driven by the shared random value.
- **Random value.** The `Config` property at defs.py 1603–1621 sums competitive submissions' integers modulo 2³⁰, raises an error if any is missing, and adds the stock-index constant `23_412_89` (line 1480).

**Divergences between rules and code** (*Basis: normative + source*):
1. **New-family guarantee.** The rules promise one pick per new family, but the code is family-blind. If the new benchmarks fit within the cap, all are selected. Otherwise a uniform sample can miss a new family. The code also applies new-first priority in every cap case, while the 2026 rules state it only for cases (c) and (d).
2. **Random generator.** The rules name C `random()`/`srandom()`; selection uses Polars `list.sample` with the same integer.
3. **Threshold boundary.** "less than one second" in the rules versus `<= 1.0` in the code.

### 11. Benchmark governance: sv-benchmarks (GitHub snapshot)

*Basis: normative (project rules) + source.*

- **Process.** Contributors fork and open a pull request, then "discuss with community members until your contribution is approved and merged" (`CONTRIBUTING.md` 30–34). The pull-request template (`.github/PULL_REQUEST_TEMPLATE` 9–22) requires a new named directory, license, attribution, a `.set` entry, a matching `.prp`, and a `.yml` task file with the expected answer. For C it also requires the data model, preprocessed sources, and a Makefile "without overly broad suppression of warnings".
- **Task files** (README lines 148–196, format 2.0) contain `format_version`, `input_files`, `properties[]` (`property_file`, `expected_verdict` true/false, optional `subproperty`), and `options.language` and `options.data_model`. At least one property with an expected result is mandatory (CONTRIBUTING lines 107–116).
- **Licensing** (lines 49–89): REUSE/SPDX headers. The license must permit commercial use, "to not exclude developers of commercial verifiers".
- **Corrections** (lines 17–23): maintainers "fix the problem in the task while keeping the task's original intention, and at the same time add a copy of the unchanged problematic task with an appropriately updated expected answer". Ideally a witness supports the change.
- **`c/check.py`** flags a missing README (line 262), files outside any category (272), contradicting verdicts (461–489), easily confused names (573), and SHA-1 duplicates (583–596).
- **Counts.** `c/` has 129 directories and 39 `.set` files. The recursive tree listing was truncated at 41,102 entries, so total counts are **not measured**.
- **Documentation slip.** README line 46 lists `causes/`, but the directory is `clauses/`.

Neither project's examined rules or code describe a blinded held-out set. sv-benchmarks relies on tasks from "several research and development groups" (README 25–33) and public review.

### 12. Guidelines from the literature

- **Chambers & Tzavella (2022).** Registered Reports are publications "in which study proposals are peer reviewed and pre-accepted before research is undertaken" (abstract).
- **Beyer, Löwe & Wendler (2019).** Six requirements (§§2.1–2.6): accurate resource measurement and limits, reliable termination, deliberate core assignment, NUMA awareness, no swapping, isolated runs.
- **Kuhn, Wallace & Gallo (2004).** Testing all n-tuples is "effectively equivalent to exhaustive testing, if software behavior is not dependent on complex event sequences and variables have a small set of discrete values".
- **Arcuri & Briand (2011).** Only the bibliographic record was verified. The transferable point is that randomized generators and checkers need many independent runs, paired by instance.

*Basis: documentation.*

### 13. Protocol: removing single-author generator bias and measuring feature coverage

*Basis: derived, from §§2–12.*

1. **Freeze before generating.** Publish a hashed record containing:
   - the factor model and t;
   - the split strategy (B or C);
   - per-stratum n and the named test;
   - the falsification bands with their refuting alternatives (§4);
   - the analysis script.
2. **Fix a random value no single party controls.** Take the sum, modulo 2³⁰, of integers committed by every generator and checker author, plus a public value fixed after those commitments. This value drives `/r:N`, the row-to-generator assignment, and instance sampling.
3. **Use at least two generators,** each by an author who did not write the checker. Assign held-out rows to generators at random and analyse generator × checker. A generator main effect larger than Δ signals bias.
4. **Measure coverage before opening results.** Measure each generator's t-way coverage of the frozen model; 100% of valid t-tuples is required on each side. Compare each factor's marginal distribution across generators against a pre-registered threshold.
5. **Gate every instance on review.** Each instance needs:
   - a machine-readable expected verdict;
   - license and provenance;
   - a hash de-duplication check;
   - a contradiction check;
   - review by someone other than its author.

   Corrections use fix-and-copy (§11). Fix trivial-instance exclusions in advance, and recuse checker-affiliated authors from decisions to remove instances.

### 14. Performance, comprehensibility, validation

| Axis | Status |
|---|---|
| L1 authoring effort | not measured |
| L2 build | PICT `make -j1 pict` 19.07 s wall, max RSS 200,360 KB, binary 379,624 bytes; TOSTER n/a (no R) |
| L3 latency | PICT 2.4–4.1 ms (t = 2–3, study model); 2.056 s at `/t:1` and 0.880 s at `/t:auto` (5¹⁰, t = 4); Python IPOG 1–6 ms; CCMCL ≈5 s per run including JVM and Xvfb start-up; exact McNemar §A ≈6 min |
| L4 not applicable | checker verdict semantics |
| L5 checker throughput | not measured |
| L6 memory / artifacts | arrays of 37–370 rows (<10 KB); generation RSS not measured |
| C1 concepts | precision 3 (p, h, α); McNemar 4 + test choice; TOST 5; Neyman 2 per stratum + floors; split: model, t, constraints, strategy. A pre-registration fits on one page: per stratum, estimator, n, test, band, refuting p1. |
| V1 | §4 band rule |
| V2 | §9 |
| V3 mechanized proof | known not to apply |
| V4 adversarial validation | not examined |

## Boundaries

- **Not examined:**
  - clustered instances and sequential designs;
  - Bayesian assurance;
  - the exact unconditional McNemar test;
  - the Neyman and Lachin primary texts (the formulas used are standard derivations);
  - IPOG-D and ACTS;
  - PICT `/b:N` and `/e`;
  - constrained IPOG;
  - the GitLab sv-benchmarks and the SV-COMP rules;
  - the SMT-COMP scrambler.
- **Unknown:**
  - whether SMT-COMP curators enforce the one-per-new-family rule manually outside `selection.py`;
  - whether TOSTER will add paired-proportion power.
- **Known not to apply:**
  - the split-loss fractions are not constants; they belong to near-minimal arrays of one model;
  - Connor's n is not an exact-test sample size;
  - TOSTER's two-proportion functions do not size paired designs.
- **Unsupported:**
  - Headless CCMCL: a static `JFrame` throws `java.awt.HeadlessException`, and on OpenJDK 27 the jar launcher fails with `NoClassDefFoundError: org/jfree/data/xy/XYDataset`.
  - A covering-index (λ ≥ 2) option: none appears in PICT's usage text.
- **Not established:**
  - that strategy C detects generator bias: it guarantees coverage only, and bias needs §13's factorial;
  - that t-way coverage makes an evaluation exhaustive, which Kuhn et al. condition on small discrete domains and no sequence dependence;
  - that any particular prior corpus is under-powered.

## Evidence

All evidence was gathered on 2026-11-20.

**Repositories** (full commits):

- `Lakens/TOSTER` @ `9ea2bf25e1a98ce0713f9aa16294872cb26b75a8`: `R/power_two_proportions.R` (9, 32–39, 79–81, 105–144, 214–261); `R/power_t_TOST.R` (96–99); `DESCRIPTION` (Version 0.9.0).
- `microsoft/pict` @ `ab76c2548f551fcb46314e58653a1bd1172f3a72`: `api/model.cpp` (85–99, 225–395); `doc/pict.md` (26–57, 88–98, 102–131); `Makefile`.
- `usnistgov/combinatorial-testing-tools` @ `e4df6c47e251800533610c48446460075fd52e3d`: `README.md` line 4; `CCM Command Line Tool/ccmcl.jar` (sha256 `4a4926312011191fb2403f070fe6bff32c1f43c9a13f4975bf931530e81a31f0`, `Rsrc-Main-Class: com.nist.ccmcl.Main`).
- `SMT-COMP/smt-comp` @ `68a5cdc72f8f5e2eb348bdfe7ab4d83842d3b54f`: `rules/rules25.md` (705–804, 1242–1249).
- `SMT-COMP/smt-comp.github.io` @ `cd15cbedd4ef312d615448100797a80e922cf575`: `smtcomp/selection.py` (32–179); `smtcomp/defs.py` (1322, 1448–1492, 1603–1621); `web/static/rules.pdf` (via `pdftotext -layout`, poppler 26.07, pp. 12–13).
- `sosy-lab/sv-benchmarks` @ `2e1723fde6aa65a250dcb677efa45edaa4b6b631` (raw files fetched from GitHub): `README.md` (10, 25–33, 46, 148–196); `CONTRIBUTING.md` (17–23, 30–34, 49–89, 107–128, 177–183); `.github/PULL_REQUEST_TEMPLATE` (9–22); `c/check.py` (262, 272, 461–489, 573–596).

**Literature** (each DOI checked on 2026-11-20 through doi.org or search).

Read in full or in the stated part:
- Fagerland, Lydersen & Laake 2013, BMC Med Res Methodol 13:91, 10.1186/1471-2288-13-91 (full text).
- Beyer, Löwe & Wendler 2019, STTT 21:1–29, 10.1007/s10009-017-0469-y (§§1–2, 5).
- Lei et al. 2007, ECBS, 10.1109/ECBS.2007.47 (NIST CSRC camera-ready PDF `ecbs-cr-final.pdf`).
- Kuhn, Wallace & Gallo 2004, IEEE TSE 30(6):418–421, 10.1109/TSE.2004.24 (NIST preprint; Table 1 not transcribed).
- Chambers & Tzavella 2022, Nat Hum Behav 6:29–42, 10.1038/s41562-021-01193-7 (abstract).
- Beyer 2012, TACAS, 10.1007/978-3-642-28756-5_38 (abstract).
- Schuirmann 1987, 10.1007/BF01068419 (landing page).

Bibliographic record only:
- Connor 1987, Biometrics 43(1):207–211, 10.2307/2531932, "Sample size for testing differences in proportions for the paired-sample design" (JSTOR challenge not passed).
- Lakens 2017, SPPS 8(4):355–362, 10.1177/1948550617697177.
- Lei et al. 2008, STVR 18(3):125–148, 10.1002/stvr.381.
- Nie & Leung 2011, ACM CSUR 43(2):11, 10.1145/1883612.1883618.
- Arcuri & Briand 2011, ICSE, 10.1145/1985793.1985795.

Cited without examination: Neyman 1934; Lachin 1992.

**Execution** (x86_64 Linux, Xeon 2.6 GHz; outputs preserved in `support/`):

```console
$ cp -r <pict checkout> /tmp/p/pict && cd /tmp/p/pict && /usr/bin/time -v make -j1 pict
  Elapsed 0:19.07, Max RSS 200360 KB, ./pict = 379,624 bytes
$ python3 support/stats_probes.py A B C D E F            > support/stats_probes_output.txt
$ python3 support/pict_probe.py /tmp/p/pict/pict /tmp/p/pict_out > support/pict_probe_output.txt
$ mkdir x && (cd x && unzip -q '<nist>/CCM Command Line Tool/ccmcl.jar')
$ python3 support/ccm_crosscheck.py /tmp/p/pict_out \
    "x:x/choco-solver-2.1.5.jar:x/JavaPlot.jar:x/jcommon-1.0.23.jar:x/jfreechart-1.0.19.jar" /tmp/p/ccm \
    > support/ccm_crosscheck_output.txt
```

`support/models/` holds the PICT models and the t = 2 arrays. The probes need only the Python standard library, plus `xvfb-run java` for CCMCL.

## Revalidation

- **Statistics.** Rerun `support/stats_probes.py` and diff against `support/stats_probes_output.txt`; the output is deterministic.
- **TOSTER.** Diff `R/power_two_proportions.R` lines 70–100 and 214–261, and run `grep -rni "mcnemar\|paired" R/` to detect a new paired function. With R available, `TOSTER::power_twoprop(p1=.5, p2=.5, null=.1, alpha=.05, power=.9, alternative="e")$n` should be about 541.1.
- **PICT.** Rebuild, then run `support/pict_probe.py`. `[0]` must report equal sets, and `[1]` must report `missing=0 invalid_rows=0`. Changed row counts are not regressions; coverage failures are. Check `Model::gcd` in `api/model.cpp` for a change of algorithm family.
- **SMT-COMP (new year).** Diff `Config` in `smtcomp/defs.py` and lines 102–179 of `smtcomp/selection.py` against that year's `rules.pdf` §6. Re-check whether `new_sample_size` is still family-blind.
- **sv-benchmarks.** The mirror is frozen. Current rules live on GitLab, which is a separate subject identified by a tag.
- **CCMCL.** Run `support/ccm_crosscheck.py`. Every row should show the probe's own fraction equal to CCMCL's.
