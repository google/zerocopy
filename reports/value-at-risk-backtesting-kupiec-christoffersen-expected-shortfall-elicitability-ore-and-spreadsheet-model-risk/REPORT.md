# Value-at-risk and expected-shortfall estimators, coverage backtests and traffic lights, and spreadsheet model risk: ORE, QuantLib, Basel MAR32/MAR33/MAR99 and documented implementation errors

## Summary

- **Empirical VaR is an order statistic whose index depends on floating-point evaluation of `N*(1-p)`.** ORE's historical-simulation VaR uses Boost.Accumulators `tail_quantile<right>`, which returns the `n`-th largest sample with `n = ceil(N*(1-p))` computed in IEEE double. Because `1 - 0.99` evaluates to `0.010000000000000009`, an integer-valued `N*(1-p)` is rounded up one step: at `N = 500, p = 0.99` the "99% VaR" is the 6th largest loss, not the 5th; at `N = 1000` it is the 11th, not the 10th. QuantLib's `GeneralStatistics::percentile(1-p)` loop lands on the same shifted order statistic. When `N*(1-p)` is not an integer (e.g. `N = 250`), both agree with exact arithmetic. Basis: source + derived (emulation).
- **ORE's `ExpectedShortfall_p` column is the mean of all P&L values at or below the `p`-quantile.** For `p < 0.5` this is the conventional lower-tail ES of P&L. For `p > 0.5` it is the mean of the body of the distribution, not a tail risk measure. ORE's own regression golden file shows `Quantile_0.99 = 846,747.82` beside `ExpectedShortfall_0.99 = -19,301.23`. An independent re-implementation reproduces every quantile in that file exactly and every ES value to within `4.2e-7`. The code matches ORE's user-guide formula. The guide's wording ("confidence level `p`", "expected loss given that the loss exceeds the VaR level") holds only for `p < 0.5`. Basis: source + documentation + execution on upstream golden data.
- **ORE's VaR backtest counts exceptions with a strict `>` against `max(VaR, threshold)`, separately for the two P&L directions ("call" and "post").** For independent observations the traffic-light bounds are binomial quantiles: `K = max(Q(s),1) - 1` with `s = 0.95` and `0.9999`.
  - For overlapping multi-day P&L, `MarketRiskBacktest` reads a configured lookup table. If the lookup fails, those bounds are left empty, a warning is logged, and only the decorrelated series is assessed, with the binomial bounds.
  - QuantExt also provides a Monte Carlo generator for such tables (default 1,500,000 samples, seed 42). The backtest does not call it.
  - The two kinds of bounds differ sharply. For 250 overlapping 10-day observations the tabulated bounds are green `<= 8` and amber `<= 24`, against `4` and `9` for independent observations.
  - `OREAnalytics/orea/engine/varbacktest.cpp` is an empty stub, and its class is commented out.

  Basis: source + execution (re-implementation).
- **Basel MAR99 Tables 1 and 2 are exact binomial arithmetic, and every displayed cell reproduces exactly.** At `N = 250` and 99% coverage the zones are green 0–4, amber 5–9 and red 10 or more. The current multipliers are 1.50 (green), 1.70/1.76/1.83/1.88/1.92 (amber) and 2.00 (red). The bank-wide backtest uses 99% one-day VaR. Desk-level backtests use 97.5% and 99% VaR and fall back to the standardised approach after more than 12 exceptions at 99% or 30 exceptions at 97.5%. Capital is based on 97.5% ES. Basis: normative + execution.
- **Coverage backtests have low power at regulatory sample sizes.** Kupiec's POF test at `N = 250`, `p = 0.01` and nominal 5% does not reject for 1–6 exceptions. Its exact size is 9.48%, and its power is 24.3% when the true exception rate is 2%. A model with a true 2% rate falls in the green zone with probability 43.9%. In a toy Monte Carlo, Christoffersen's independence test detected first-order exception clustering only 15–44% of the time. Basis: derived (exact) + execution (toy model).
- **Coherence and elicitability pull in different directions.** VaR is elicitable but not coherent, because it is not subadditive. ES is coherent (Artzner et al.; Acerbi–Tasche) but not elicitable on its own (Gneiting 2011). The pair (VaR, ES) is jointly elicitable (Fissler–Ziegel 2016). A count of exceptions therefore cannot validate an ES model by itself. Basis: documentation (peer-reviewed results).
- **Implementation-error evidence:**
  - Field audits since 1995 found errors in 94% of 88 audited spreadsheets, and cell error rates ranged from 0.4% to 6.9% (Panko, 2005 revision).
  - 24% of Enron spreadsheets with at least one formula contain an Excel error (Hermans–Murphy-Hill).
  - A coding error in the Reinhart–Rogoff working spreadsheet excluded five countries. That error accounted for only −0.3 percentage points of the gap between −0.1% and 2.2% growth in the highest-debt category; selective exclusion and weighting explain most of the rest (Herndon–Ash–Pollin).
  - JPMorgan's task force found that the new CIO VaR model "understated the risks", was approved with "only limited back-testing", and that unvetted spreadsheet formula changes in price testing "introduced two calculation errors".
  - SR 11-7 (2011) called spreadsheets "particularly prone to model risk". **SR 26-2 (April 17, 2026) supersedes SR 11-7** and excludes "simple arithmetic calculations, such as those found within spreadsheets" from the term "model".

## Applicability

The subjects relate as follows.

- **ORE** (`OpenSourceRisk/Engine` at `3d75a69087911a7e2cf1e6882da7bc27135c0762`, the v1.8.17.0 GitHub merge) is the primary implementation examined. It covers historical-simulation and parametric VaR, the `MarketRiskBacktest` exception counter, and the QuantExt stop-light bound functions.
- **Boost.Accumulators** (`boostorg/accumulators` at `6bd97b3843f3488af28c18aa9d0f06275b6c6c75`) is examined only for `tail_quantile`, because ORE delegates its quantile rule there. ORE builds against whatever Boost is installed, so the pinned Boost revision is an assumption about the estimator. The formula has been stable in that header, but other Boost versions were not checked.
- **QuantLib** (`lballabio/QuantLib` at `1e3cad8eb393e6e92bed91705c25c461197896ca`) is a second, independent estimator family (`GenericRiskStatistics`).
- **The Basel Framework chapters** are the normative backtesting regime. The pages were retrieved with the URL parameters `inforce=20230101&published=20200327`. Paragraph numbers MAR32.5, MAR32.18, MAR32.19 and MAR33.3 refer to that rendering.
- **The papers** supply the test statistics (Kupiec; Christoffersen) and the theory (coherence; elicitability).
- **The spreadsheet and model-risk sources** are separate evidence about how implementation errors arise and which controls the sources themselves name. They do not concern ORE or QuantLib.

Scope limits:

- ORE and QuantLib were **not compiled or run**. Statements about their numeric behaviour come from source, from ORE's committed regression outputs, and from re-implementations of the read algorithms.
- "Call" and "post" in ORE's backtest are its names for the two P&L directions: `pnl` and `-pnl`. The class is shared with initial-margin backtesting.
- Results about P&L sign assume ORE's historical P&L convention: scenario NPV minus base NPV, with positive values as gains (`HistoricalPnlGenerator::pnl`, `historicalpnlgenerator.cpp` lines 364–367: `pnl -= cube_->getT0(...)`, `pnl += cube_->get(...)`).
- The Monte Carlo results (Christoffersen power, overlapping bounds) are **toy-model or re-implementation results**. They are not measurements of ORE.

## Findings

### 1. Risk-measure definitions and sign conventions

Let `X` be P&L, with gains positive, and let `α` be the tail probability (0.01 for 99% VaR).

| Measure | Definition used here | ORE `HistoricalSimulationVarCalculator` | QuantLib `GenericRiskStatistics` |
| :--- | :--- | :--- | :--- |
| VaR | `VaR_α = -q_α(X)` (a loss, positive when `q_α < 0`) | `var(p)` returns the right-tail order statistic of `X` (or of `-X` when `isCall=false`) at probability `p`; the sign is left to the caller, and requesting `p=0.01` returns the lower P&L quantile (negative when it is a loss) | `valueAtRisk(c) = -min(percentile(1-c), 0)`; requires `c ∈ [0.9, 1)`; floored at 0 |
| ES | `ES_α = -(1/α)(E[X·1{X≤q_α}] + q_α(α - P[X≤q_α]))` (Acerbi–Tasche) | `expectedShortfall(p)` = mean of `{x : x ≤ var(p)}` (ties included) | `expectedShortfall(c) = -min(E[x | x < -VaR(c)], 0)` (strict `<`; the VaR point excluded) |
| Domain guard | — | none on `p` beyond Boost's index check | `QL_REQUIRE(centile>=0.9 && centile<1.0, ...)` |

QuantLib's doc comment states the formula `E[x | x < VaR(p)]` (`riskstatistics.hpp` line 89). The code uses `x < -VaR(p)`: `Real target = -valueAtRisk(centile);` (line 196). The comment's sign convention is therefore looser than the code. QuantLib's `RiskStatistics` is `typedef GenericRiskStatistics<GaussianStatistics> RiskStatistics;` (line 123). Its `percentile()` is nonetheless the empirical `GeneralStatistics::percentile`, which returns the first sorted sample whose cumulative weight reaches `percent*sampleWeight` (`generalstatistics.cpp` lines 88–110). The Gaussian closed forms are separate methods (`gaussianValueAtRisk`, `gaussianExpectedShortfall`).

Basis: source.

### 2. Which order statistic is the "99% VaR"?

Boost's estimator (`tail_quantile.hpp` lines 70–85) reads:

```cpp
std::size_t n = static_cast<std::size_t>(
    std::ceil(
        cnt * ( ( is_same<LeftRight, left>::value ) ? args[quantile_probability] : 1. - args[quantile_probability] )
    )
);
if ( n < static_cast<std::size_t>(tail(args).size()))
{
   return *(boost::begin(tail(args)) + n - 1);
}
```

ORE calls it with a right tail and a cache of `floor(N*(1-p)+0.5)+2` samples (`historicalsimulationvar.cpp` lines 266–280). The emulation below compares the order statistic each library selects with exact arithmetic `ceil(N(1-p))`. The column "QuantLib k" is the 1-based index from the bottom, counted the same way.

| N | p | exact `ceil(N(1-p))` | ORE/Boost `n` | QuantLib `k` | `N*(1-p)` in double |
| ---: | ---: | ---: | ---: | ---: | :--- |
| 100 | 0.99 | 1 | 2 | 2 | 1.0000000000000009 |
| 250 | 0.99 | 3 | 3 | 3 | 2.500000000000002 |
| 500 | 0.99 | 5 | **6** | **6** | 5.000000000000004 |
| 715 | 0.99 | 8 | 8 | 8 | 7.150000000000007 |
| 1000 | 0.99 | 10 | **11** | **11** | 10.000000000000009 |
| 1000 | 0.975 | 25 | **26** | **26** | 25.00000000000002 |
| 2000 | 0.975 | 50 | **51** | **51** | 50.00000000000004 |

Two further properties follow from the same source:

- **Lower quantiles.** For `p < 0.5` the Boost right-tail estimator returns the `(N - ceil(N(1-p)) + 1)`-th smallest sample. At `N = 500, p = 0.01` this is the 6th smallest, whereas the left-continuous convention `X_(ceil(Np))` gives the 5th.
- **Tiny samples.** The `n < tail.size()` check is strict, so the sample minimum can never be returned as a lower quantile, and very small samples yield `NaN`. ORE's committed intraday-power example output shows `#N/A` in its `Quantile_0.01` and `Quantile_0.05` columns. Whether that output is caused by this check was **not examined**.

Basis: source + derived (`support/var_backtest_exact.py`, `support/ore_hsvar_golden_check.py`).

### 3. ORE's `ExpectedShortfall_p` semantics, checked against ORE's own golden output

Source (`historicalsimulationvar.cpp` lines 282–299):

```cpp
const auto var = this->var(confidence, isCall, tradeIds);
...
for (const auto pnl : pnls_) {
    const auto adjustedPnl = isCall ? pnl : -pnl;
    if (adjustedPnl <= var) {
        accumulator(adjustedPnl);
    }
}
return mean(accumulator);
```

The user guide (`Docs/UserGuide/methods/marketrisk.tex` lines 593–600) gives the same formula, `ES(p) = (1/|L(p)|) Σ_{j∈L(p)} π_F(j)` with `L(p) = {j : π_F(j) ≤ VaR(p)}`. It describes this as ES "at confidence level `p`", i.e. "the expected loss given that the loss exceeds the VaR level".

The committed regression example `Examples/MarketRisk/ExpectedOutput/HistSimVar/` has these properties:

- `historical_PnL.csv` has SHA-256 `f69e5aad60ad8b187557ed526aaf4d06d8ba0ad9288cfe490e68b5ce927dda5d` and contains 715 scenarios per group.
- `var.csv` has SHA-256 `0a2560b8250cc12fe44785a86b53053d2f289aded94a971e86f85f5abca1485e`.
- `var.csv` requests the quantiles 0.01, 0.05, 0.95 and 0.99, each with an ES column.

Recomputed for group `All/All/All`:

| p | ORE `n` | ORE quantile | ORE ES | re-implemented ES | samples averaged | lower-tail mean (k smallest) | upper-tail mean (k largest) |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 0.01 | 708 | −874,503.35 | −949,845.99 | −949,845.99 | 8 | −949,845.99 (k=8) | 933,541.33 |
| 0.05 | 680 | −629,899.12 | −777,808.70 | −777,808.70 | 36 | −777,808.70 (k=36) | 701,059.87 |
| 0.95 | 36 | 552,878.31 | **−46,660.24** | −46,660.24 | 680 | — | 701,059.87 (k=36) |
| 0.99 | 8 | 846,747.82 | **−19,301.23** | −19,301.23 | 708 | — | 933,541.33 (k=8) |

All six groups match: the quantile discrepancy is `0`, and the largest ES discrepancy is `4.17e-7`, consistent with the 6-decimal rounding of the inputs.

- **For `p ≤ 0.05`** the column equals the mean of the `ceil(Np)` smallest P&L values, which is the lower-tail ES of P&L.
- **For `p ≥ 0.95`** it is the mean of 680–708 samples, the body of the distribution. A reader who takes "`ExpectedShortfall_0.99`" to be 99% ES receives a number of the wrong order of magnitude and the wrong sign.

The lower-tail column also differs slightly from Acerbi–Tasche's fractional definition. At `α = 0.01` and `N = 715`, the possible estimators give:

| Estimator | Value |
| :--- | ---: |
| Mean of the `floor(Nα)=7` smallest | −960,609.22 |
| Fractional weighting `(Σ_{i≤7} x_(i) + 0.15·x_(8))/7.15` | −958,802.80 |
| ORE (mean of 8 smallest) | −949,845.99 |

The ORE value differs from the fractional one by about 0.9%.

Basis: source + documentation + execution (`support/ore_hsvar_golden_check.py`, `support/ore_hsvar_golden_check.out`).

### 4. ORE parametric VaR

`ParametricVarCalculator::var` (`parametricvar.cpp` lines 107–130) dispatches on five methods:

- `Delta`
- `DeltaGammaNormal`
- `MonteCarlo`
- `Cornish-Fisher`, which uses moment matching on the delta-gamma P&L
- `Saddlepoint`

The Saddlepoint branch catches any exception and silently substitutes Monte Carlo; the only trace is a log line:

```cpp
} catch (const std::exception& e) {
    ALOG("Saddlepoint VaR computation exited with an error: " << e.what() << ", falling back on Monte-Carlo");
    res = QuantExt::deltaGammaVarMc<PseudoRandom>(omega_, delta, gamma, confidence, parametricVarParams_.samples,
                                                parametricVarParams_.seed, covarianceSalvage_);
}
```

This fallback has two weaknesses visible in source:

- The explicit `MonteCarlo` branch checks `samples` and `seed` for `Null<Size>()` (lines 112–115). The fallback does not.
- `ParametricVarParams::samples` defaults to `Null<Size>()` (`parametricvar.hpp` line 65), and `deltaGammaVarMc` performs no paths check before using `paths` in a loop bound and a cache size (`deltagammavar.hpp`).

What happens when the fallback runs without configured samples is **unknown**; it was not executed. A diagnostic-legibility defect is visible in source: the seed check at line 114 reports `"method MonteCarlo requires mcSamples"`, the same message as the samples check.

Basis: source.

### 5. Coherence, elicitability, and what each implies for validation

- **Coherence** (Artzner, Delbaen, Eber, Heath 1999) requires monotonicity, translation invariance, positive homogeneity and subadditivity. VaR violates subadditivity in general. Acerbi–Tasche (2002) show that ES, defined with the fractional correction term above, is coherent for general distributions, including those with atoms. The naive "mean below VaR" can fail coherence when the distribution has atoms at the quantile. Finite-sample estimators such as ORE's and QuantLib's implement variants of the naive form.
- **Elicitability.** A functional is elicitable if some scoring function is strictly consistent for it. Elicitability allows competing forecasts to be ranked by average realised score.
  - Quantiles (hence VaR) are elicitable, via the pinball loss.
  - ES alone is not elicitable (Gneiting 2011).
  - (VaR, ES) is jointly elicitable (Fissler–Ziegel 2016).
- **Consequences for checks.**
  1. An exception count tests a VaR forecast's calibration (Kupiec) and its exception-sequence structure (Christoffersen).
  2. No statistic computed from exceptions alone can show that an ES forecast is correct. ES checks need either the conditional loss magnitudes (as in Acerbi–Székely-type tests, **not examined**) or joint (VaR, ES) scoring.
  3. The Basel design reflects this split. Capital is based on 97.5% ES (MAR33.3: "In calculating ES, a bank must use a 97.5th percentile, one-tailed confidence level"), yet model eligibility is decided by backtesting VaR (MAR32.5, MAR32.18–32.19) plus P&L attribution tests.

Basis: documentation (peer-reviewed results) + normative (MAR).

### 6. Coverage tests: statistics, exact size and power

The tests use the following statistics. Here `x` is the number of exceptions out of `N` and `π̂ = x/N`. The `n_ij` count transitions from state `i` to state `j` in the exception indicator sequence.

- **Kupiec unconditional coverage:** `LR_uc = -2[ x ln p + (N-x) ln(1-p) - x ln π̂ - (N-x) ln(1-π̂) ] ~ χ²₁` asymptotically.
- **Christoffersen independence:** `LR_ind = -2[ ln L(π) - ln L(π01, π11) ] ~ χ²₁`, with `π01 = n01/(n00+n01)`, `π11 = n11/(n10+n11)` and `π = (n01+n11)/(n00+n01+n10+n11)`.
- **Conditional coverage:** `LR_cc = LR_uc + LR_ind ~ χ²₂`.

Exact finite-sample behaviour of Kupiec's test at `p = 0.01` with the χ²₁ 5% critical value 3.8415, computed by enumerating the binomial distribution:

| N | non-rejection region | exact size | power at 2% | power at 3% | power at 4% | power at 5% |
| ---: | :---: | ---: | ---: | ---: | ---: | ---: |
| 250 | 1 ≤ x ≤ 6 | 0.0948 | 0.2427 | 0.6255 | 0.8750 | 0.9686 |
| 500 | 2 ≤ x ≤ 9 | 0.0709 | 0.5438 | 0.9331 | 0.9956 | 0.9998 |
| 1000 | 5 ≤ x ≤ 16 | 0.0551 | 0.7815 | 0.9965 | 1.0000 | 1.0000 |

At `N = 250` zero exceptions is itself a rejection (`LR_uc(0) = 5.03`), and the asymptotic test is anti-conservative: its size is 9.48% rather than 5%.

Toy Monte Carlo, `N = 250`, 20,000 replications per scenario, seed 20261120, Monte Carlo standard error `≤ 0.0035`. Each cell is the rejection rate at nominal 5%.

| Data-generating process | LR_uc | LR_ind | LR_cc | mean exceptions |
| :--- | ---: | ---: | ---: | ---: |
| iid, rate 1% (correct) | 0.0969 | 0.0147 | 0.0081 | 2.497 |
| iid, rate 2% | 0.2404 | 0.0188 | 0.1527 | 5.000 |
| iid, rate 3% | 0.6216 | 0.0146 | 0.4991 | 7.475 |
| Markov, rate 1%, `P(I_t=1 \| I_{t-1}=1) = 0.1` | 0.1253 | 0.1542 | 0.0756 | 2.506 |
| Markov, rate 1%, `π11 = 0.2` | 0.1690 | 0.2859 | 0.1672 | 2.525 |
| Markov, rate 1%, `π11 = 0.4` | 0.2867 | 0.4420 | 0.3410 | 2.512 |

The simulated LR_uc size (0.0969) agrees with the exact value (0.0948) within Monte Carlo error. With about 2.5 expected exceptions per year, `n11` is almost always 0. The independence test therefore has little information: it is under-sized under the null (1.5%) and detects strong clustering (`π11 = 0.4`, forty times the base rate) less than half the time. These are properties of the tests at this sample size, measured on a toy data-generating process, not properties of any bank model.

Basis: derived (exact, `support/var_backtest_exact.py`) + execution (toy, `support/christoffersen_toy.py`).

### 7. Basel traffic lights (MAR99, MAR32)

MAR99 "Table 1" lists binomial probabilities for 250 independent observations under true coverage of 99%, 98%, 97%, 96% and 95%, as exact, type 1 or type 2 probabilities. "Table 2" gives the zones and cumulative probabilities. Every cell in both tables reproduces exactly:

- Cumulative probabilities at 99%, for 0–10 exceptions: 8.11%, 28.58%, 54.32%, 75.81%, 89.22%, 95.88%, 98.63%, 99.60%, 99.89%, 99.97%, 99.99%.
- The type 1 error of a "5 or more" cut-off is 10.8%.
- The type 2 error at 97% coverage is 12.8%.

| Zone | Exceptions (N=250) | Backtesting-dependent multiplier (MAR99 Table 2) | P(zone \| true rate 1%) | 2% | 3% | 4% | 5% |
| :--- | :---: | :--- | ---: | ---: | ---: | ---: | ---: |
| Green | 0–4 | 1.50 | 0.8922 | 0.4387 | 0.1282 | 0.0270 | 0.0046 |
| Amber | 5–9 | 1.70, 1.76, 1.83, 1.88, 1.92 | 0.1076 | 0.5309 | 0.6508 | 0.4284 | 0.1900 |
| Red | ≥ 10 | 2.00 | 0.0003 | 0.0304 | 0.2210 | 0.5446 | 0.8054 |

Normative rules from MAR32:

- **MAR32.5:** the bank-wide backtest uses a 99% one-day VaR. Exceptions for actual and hypothetical P&L are counted separately, and "the overall number of exceptions is the greater of these two amounts". Missing P&L or VaR "will count as an outlier".
- **MAR32.18:** desk-level backtests compare one-day VaR at "both the 97.5th percentile and the 99th percentile".
- **MAR32.19:** a desk with "more than 12 exceptions at the 99th percentile or 30 exceptions at the 97.5th percentile" moves to the standardised approach.

Under a correct model with iid exceptions, those desk thresholds are rarely reached. `P(X > 12 | 250, 1%) = 1.94e-6` and `P(X ≥ 30 | 250, 2.5%) = 2.16e-12`. The desk tests are therefore practical-significance screens, not size-controlled tests.

Basis: normative + derived (exact).

### 8. ORE's backtest implementation

- **Exception rule.** `marketriskbacktest.cpp` lines 257–260:
  - `if (callScenPnls[i] > std::max(sr.callValue, btArgs_->exceptionThreshold_)) sr.callExceptions++;`
  - `if (-postScenPnls[i] > std::max(sr.postValue, btArgs_->exceptionThreshold_)) sr.postExceptions++;`

  The comparison is strict, and a configurable absolute threshold floors the VaR. A P&L exactly equal to VaR is not an exception. Basel's "exceeds" wording is consistent with this.
- **Iid bounds.** The binomial branch (`stoplightbounds.cpp` lines 164–197) computes `res.push_back(std::max(static_cast<Size>(boost::math::quantile(b, s)), (Size)(1)) - 1);`. Boost.Math's binomial quantile defaults to rounding upper quantiles outward, so `Q(s)` is the smallest `k` with `P(X ≤ k) ≥ s`, and the bound is the largest `k` with `P(X ≤ k) < s`. The emulation reproduces Basel's 4/9 at `N = 250`, and gives 8/14 at `N = 500` and 14/23 at `N = 1000`. ORE's unit test `testIidBoundsAgainstReferenceResults` checks `{4, 9}` and the eleven 1996 cumulative probabilities to `1e-4` (`QuantExt/test/stoplightbounds.cpp` lines 111–126).
- **Overlapping, correlated P&L.**
  - **Monte Carlo branch** (lines 99–162). It simulates `observations + numberOfDays - 1` iid normal daily P&Ls and forms rolling `n`-day sums. It counts exceedances of `h = Φ⁻¹(p)·sqrt(n)` and takes the Boost tail quantile of the counts, minus 1. Defaults are `samples = 1500000` and `seed = 42` (`stoplightbounds.hpp` lines 59–64).
  - **Tabulated branch** (lines 80–97). It is used when the levels are `{0.95, 0.9999}`, `p = 0.99`, the horizon is 1 or 10 days and a table is configured; otherwise it calls `QL_FAIL`.
  - **How `MarketRiskBacktest` uses the two branches** (`marketriskbacktest.cpp` lines 305–334). For overlapping scenarios it calls only the tabulated branch. It looks up the configured margin-period-of-risk horizon and falls back to the 10-day table row. If that lookup fails, a structured warning is logged and `sr.bounds` keeps its empty initial value (`SummaryResults` is initialised with `{}` for `bounds`, `marketriskbacktest.cpp` line 194 and `.hpp` line 113). The decorrelated series is always assessed with the iid binomial bounds. The Monte Carlo branch is not called from the backtest; it serves table generation and unit tests.
  - **Decorrelation.** `decorrelateOverlappingPnls` multiplies by `L⁻¹`, where `L` is the Cholesky factor of the correlation matrix `c_ij = 1 - |i-j|/n` (lines 281–334). It assumes that daily P&Ls are iid.
- **Re-implementation of the Monte Carlo branch** (numpy PCG64 random numbers rather than ORE's generator; 400,000 samples; seed 42). The re-implementation is not ORE.

| Observations | Re-implementation (max green, max amber) | ORE tabulated (from the unit-test table) | iid bounds |
| ---: | :---: | :---: | :---: |
| 200 | (7, 22) | (7, 22) | — |
| 250 | (8, 23) | (8, 24) | (4, 9) |
| 300 | (9, 25) | (9, 26) | — |
| 500 | (13, 32) | (13, 32) | (8, 14) |

  The green bounds agree. The amber bounds differ by at most 1, which is expected from Monte Carlo error at the 0.9999 quantile: only about 40 samples lie beyond it. ORE's own test file says the same about its tabulated values: "FIXME the test fails on several tabulated values, both with 5m and 50m samples" (line 129), and the full-table test is `disabled()` (line 130).
- **Placeholder class.** `varbacktest.hpp` contains only commented-out code (lines 31–33: `//class VarBacktest: public MarketRiskBacktest {`). `varbacktest.cpp` defines an empty namespace.
- **Unit tests.** No OREAnalytics unit-test file for `HistoricalSimulationVarCalculator`, the ES column or `MarketRiskBacktest` was found at the pinned revision (search by file name). The committed example outputs are the regression check.

Basis: source + execution (re-implementation, `support/overlap_stoplight_reimpl.py`).

### 9. Documented spreadsheet and model-implementation errors and the controls each source names

| Source | Error (as documented) | Type | Control the source associates with it |
| :--- | :--- | :--- | :--- |
| Panko (2005 revision of the 1998 paper) | "94% of the 88 spreadsheets audited in 7 studies have contained errors"; cell error rates in four field audits "range from 0.4% to 6.9%" | Cell-level formula and logic errors | Code inspection; the paper notes that "single-person code inspection ... misses some errors" and argues for programming-style development disciplines |
| Hermans & Murphy-Hill (ICSE 2015) | "24% of Enron spreadsheets with at least one formula contain an Excel error"; 10% of emails refer to or send spreadsheets, and emails "frequently" discuss errors and updates | Error values and formula smells (long calculation chains) | Smell detection and analysis tooling (the paper's operational definition of "Excel error" was **not examined**) |
| Herndon, Ash, Pollin (working paper 322, 2013) | "A coding error in the RR working spreadsheet entirely excludes five countries, Australia, Austria, Belgium, Canada, and Denmark"; together with other errors it accounts for "a -0.3 percentage-point error" in the highest-debt category, where the corrected mean is "2.2 percent, not -0.1 percent" | Formula range/reference error, plus selective data exclusion and unconventional weighting (methodological, not spreadsheet mechanics) | Independent replication from the working spreadsheet; publication of the working files |
| JPMorgan task force (Jan 2013) | The new CIO VaR model "understated the risks" and "suffered from significant operational shortcomings"; approvers "required only limited back-testing" (PDF p. 17–18); spreadsheet formula changes in price testing "not subject to an appropriate vetting process, inadvertently introduced two calculation errors" (PDF p. 60); the price-testing process relied on unvetted spreadsheets with "time-consuming manual inputs to entries and formulas" (PDF p. 101); the firm "reverted back to its prior VaR model" on May 10 (PDF p. 77) | Untested model change; manual copy/entry; unvetted formula edit | Backtesting before approval; vetting of spreadsheet changes; risk-function engagement in model implementation |
| SR 11-7 (2011; FDIC adoption text) | "User-developed applications, such as spreadsheets ... are particularly prone to model risk" | All | Validation = "conceptual soundness", "ongoing monitoring, including process verification and benchmarking", "outcomes analysis, including back-testing"; code under "rigorous quality and change control"; "effective challenge" |
| SR 26-2 (April 17, 2026) | Supersedes SR 11-7; the term "model" "excludes simple arithmetic calculations, such as those found within spreadsheets" | Scope change | Keeps "effective challenge", conceptual soundness and outcomes analysis ("back-testing or outlier analysis"); emphasises a risk-based approach; the letter is "expected to be most relevant to banking organizations with over \$30 billion in total assets" |

Two cautions apply to these sources.

- **The headline number in Herndon–Ash–Pollin is not mainly a spreadsheet error.** By the authors' own decomposition, the spreadsheet coding error explains only −0.3 of the 2.3 percentage-point gap.
- **The figure most often quoted about the JPMorgan VaR model was not verified.** Appendix A of the task-force report, where secondary sources locate the spreadsheet formula error, was **not retrievable** with the tools used (the extracted text ends at PDF page 106). That error is reported as the hazard-rate change being divided by the sum rather than the average.

Basis: documentation (primary reports, quoted).

### 10. Performance and resource footprint (six levels)

| Level | ORE | QuantLib | This investigation's probes |
| :--- | :--- | :--- | :--- |
| L1 authoring/maintenance | `varbacktest.*` is a 25 + 36 line placeholder; `stoplightbounds.cpp` 336 lines; `marketriskbacktest.cpp` 499 lines (measured, `wc -l`); person-months **not measured** | `riskstatistics.hpp` 229 lines (measured); effort **not measured** | The four probe scripts total 401 lines (measured, `wc -l`); token or turn budgets **not measured** |
| L2 build | Repository 221,807 KB (GitHub API `size`); build time and memory **not measured** | Repository 89,398 KB (GitHub API); build **not measured** | No build needed (Python 3.13 standard library; numpy 2.3.5 for one probe) |
| L3 per-run latency | QuantExt Monte Carlo bounds at default settings: 1.5e6 samples × (`observations + 9`) normals per call (derived from defaults); wall time **not measured** | Not applicable | Exact binomial probe 0.05 s wall; Christoffersen toy (6 × 20,000 replications) 4.9 s; overlapping re-implementation (4 × 400,000 samples) 15.9 s (measured with `/usr/bin/time` on a 96-core x86-64 Linux workstation, single-threaded Python except numpy) |
| L4 generated-code execution | HS VaR keeps a tail cache of `floor(N(1-p)+0.5)+2` samples and an O(N) mean pass for ES (derived from source) | `percentile` sorts the sample set (O(N log N), derived) | Not applicable |
| L5 checker speed | Unit test `testSinglePortfolioAgainstReferenceResults` uses 5,000,000 samples; the full-table test is disabled because it takes "apprx. 4 min" (source comment) | Not measured | Golden check over 4,290 P&L rows 0.03 s wall (measured) |
| L6 memory/disk | Golden `historical_PnL.csv` 231,886 bytes (GitHub tree listing); runtime RSS **not measured** | Not measured | Peak RSS: golden check 11.9 MB, exact binomial probe 11.8 MB, Christoffersen toy 9.5 MB, overlapping re-implementation 851 MB (measured, `/usr/bin/time %M`) |

### 11. Human comprehensibility (C1) and conceptual simplicity (C2)

- **C1: hidden convention load.** Before interpreting a "99% VaR" or "ES" figure, a reader must hold five independent conventions in mind:
  1. the P&L sign;
  2. whether `p` is a confidence level or a quantile level;
  3. which order statistic is chosen, including the floating-point shift;
  4. whether ties at the quantile enter the ES average (ORE `≤`, QuantLib `<`);
  5. flooring at zero (QuantLib).

  ORE's column names `Quantile_p` and `ExpectedShortfall_p` encode only the second, and its documentation describes it inconsistently. The resulting failure is silent: a body mean appears in a column labelled ES.
- **C1: diagnostics.** Several failure paths are hard to see:
  - the Saddlepoint-to-Monte-Carlo fallback, whose only trace is an `ALOG` line;
  - a copy-pasted error message for the missing seed;
  - tabulated stop-light failures, which become a structured warning while the backtest proceeds.
- **C2: one invariant, several mechanisms.** The traffic-light zone is one invariant: the largest `k` with `P(X ≤ k) < s`. ORE realises it three ways, with different exactness: an exact binomial quantile, Monte Carlo with its own tail-quantile convention, and a configured table. A single exact computation of the overlapping-window count distribution would make the Monte Carlo and the table special cases rather than independent sources of truth. That computation would be dynamic programming over the window state, or a Markov-chain embedding (not examined).
- **C2: what can be scored.** Elicitability theory yields the minimal abstraction. A forecast is backtestable by scoring if and only if it is reported together with the functional that makes it elicitable: a quantile alone, or VaR together with ES. Reporting ES alone moves the validation burden onto ad-hoc tests.

### 12. Validation of implementations and proposed checks (V1–V4)

- **V1, specification adequacy and non-vacuity.**
  - ORE's regression example passes against its own golden file, but that file encodes the body-mean ES column for `p > 0.5`. A golden test cannot detect a specification error it has frozen.
  - QuantLib's `riskstats.cpp` test compares empirical VaR and ES on 65,535 Sobol-generated Gaussian samples with Gaussian closed forms, with ES tolerance `|expected| × 1e-2` (`test-suite/riskstats.cpp` lines 396–401). At that sample size and tolerance it cannot detect a one-order-statistic shift.
  - A mutation-style check would assert `ES_α ≥ VaR_α` (in loss units). On ORE's golden output that assertion fails for the 0.95 and 0.99 columns.
- **V2, differential testing.**
  - The re-implementations here act as differential oracles for ORE's ES and quantile path (exact agreement) and for the stop-light Monte Carlo (agreement up to Monte Carlo error).
  - Exact binomial enumeration is an oracle for MAR99's tables (exact agreement).
  - No cross-library differential test between ORE and QuantLib exists in either repository (**not examined** beyond file-name search).
- **V3, concurrency, crash or physical validation:** not applicable to these single-threaded statistics. ORE's multi-threaded revaluation (`MultiThreadArgs`) was **not examined**.
- **V4, field replay and human behaviour.**
  - The regulatory process replays realised P&L against reported VaR, which is the outcome analysis named in SR 11-7 and SR 26-2.
  - The JPMorgan record shows the human failure mode: a model change that halved reported risk was approved with "limited back-testing".
  - No source examined measured how often practitioners misread VaR or ES conventions; this is **not examined**.

## Boundaries

- **Not executed: ORE and QuantLib binaries.** All ORE and QuantLib numeric statements come from source reading, committed golden files and re-implementations. The re-implementations reproduce the golden file exactly, which supports but does not prove that the shipped binary follows the same path for other inputs.
- **Not examined: Boost versions other than the pinned revision.** The order-statistic shift depends on the `ceil(cnt*(1.-p))` expression; a Boost release that changed it would change ORE's VaR index.
- **Unknown:** what the Saddlepoint fallback does when `samples` is unset, and whether the intraday-power example's `#N/A` cells come from Boost's strict index check.
- **Not examined: other estimator surfaces.** These include ES in ORE's parametric path, the Taylor/sensitivity VaR path beyond its shared estimator, and ORE's SIMM backtesting use of `MarketRiskBacktest`.
- **Not examined: ES backtests.** Acerbi–Székely tests, duration-based tests (Christoffersen–Pelletier) and comparative backtests with joint scores were not examined, and no power numbers are given for them.
- **Not examined: the 1996 Basel document.** The 1996 backtesting document (the multiplication factor 3 plus 0.40–1.00 add-ons) was not retrieved. Only the current MAR99 multipliers are reported. The 1996 cumulative probabilities appear in ORE's unit test as quoted from that document.
- **Not examined: JPMorgan Appendix A.** The "sum instead of average" formula error and the magnitude of the VaR reduction are attributed to Appendix A by secondary sources only.
- **Version caveat for Panko.** The quoted Panko figures come from the January 2005 revision; the 1998 journal article (the DOI) is shorter and was not compared.
- **Version caveat for Herndon–Ash–Pollin.** Their figures come from the April 2013 working paper; the 2014 journal version was not compared.
- **Stronger conclusions not established:**
  - that ORE's ES column is "a bug". It is the documented formula, and it is correct for `p < 0.5`.
  - that the order-statistic shift materially changes capital. It changes one order statistic, and its magnitude depends on the tail gap.
  - that ORE's tabulated overlapping bounds are wrong. They agree with an independent re-implementation within Monte Carlo error.

## Evidence

Observation date: all evidence was acquired on 2026-11-20 (UTC). All five GitHub repositories were pinned to their HEAD commits on that date.

- **ORE** (`OpenSourceRisk/Engine` at `3d75a69087911a7e2cf1e6882da7bc27135c0762`):
  - `OREAnalytics/orea/engine/historicalsimulationvar.cpp` 266–299 (VaR and ES);
  - `.../historicalsimulationvar.hpp` (default `isCall = true`);
  - `.../historicalpnlgenerator.cpp` 349–369 (P&L sign);
  - `.../parametricvar.cpp` 107–130, `.../parametricvar.hpp` 61–65;
  - `.../marketriskbacktest.cpp` 190–337 (exceptions, bounds), `.../marketriskbacktest.hpp` 75–96 (`ragLevels_ = {0.95, 0.9999}`);
  - `.../varbacktest.hpp` 31–33 and `.../varbacktest.cpp` (empty);
  - `QuantExt/qle/math/stoplightbounds.hpp` 39–90, `QuantExt/qle/math/stoplightbounds.cpp` 80–334;
  - `QuantExt/qle/math/deltagammavar.hpp` / `.cpp`;
  - `QuantExt/test/stoplightbounds.cpp` 45–130;
  - `Docs/UserGuide/methods/marketrisk.tex` 578–600;
  - `Examples/MarketRisk/ExpectedOutput/HistSimVar/{historical_PnL.csv,var.csv}` (SHA-256 above).
- **QuantLib** (`lballabio/QuantLib` at `1e3cad8eb393e6e92bed91705c25c461197896ca`): `ql/math/statistics/riskstatistics.hpp` 82–123, 178–205; `ql/math/statistics/generalstatistics.cpp` 88–110; `test-suite/riskstats.cpp` 36–72, 300–401.
- **Boost.Accumulators** (`boostorg/accumulators` at `6bd97b3843f3488af28c18aa9d0f06275b6c6c75`): `include/boost/accumulators/statistics/tail_quantile.hpp` 70–98.
- **Basel Framework**, retrieved with `inforce=20230101&published=20200327`: MAR99 Tables 1–2; MAR32.4–32.6, 32.18–32.19; MAR33.3.
- **Supervisory guidance**: SR 11-7 text as FDIC attachment `fil17022a.pdf` (validation elements; the spreadsheet sentence); SR 26-2 (April 17, 2026), cover letter and attachment §§ I–III.
- **Papers**, each verified by DOI lookup to the publisher or an index page: Kupiec 1995; Christoffersen 1998 (*IER* 39(4), 841–862); Artzner et al. 1999; Acerbi–Tasche 2002; Gneiting 2011; Fissler–Ziegel 2016; Panko 1998/2005; Hermans–Murphy-Hill 2015 (ICSE vol. 2, pp. 7–16); Herndon–Ash–Pollin 2014/2013.
- **JPMorgan task force report**, EliScholar copy: PDF pages 17–18, 60, 77, 101 (printed page = PDF page − 4). The extracted text ends at PDF page 106, so Appendix A (printed pages 121 onward) was not available.
- **Execution.** Python 3.13 on x86-64 Linux; numpy 2.3.5 for the overlapping re-implementation only. Scripts and outputs are in `support/`:
  - `var_backtest_exact.py` → `var_backtest_exact.out`
  - `ore_hsvar_golden_check.py historical_PnL.csv var.csv` → `ore_hsvar_golden_check.out`
  - `christoffersen_toy.py 20000 20261120` → `christoffersen_toy.out`
  - `overlap_stoplight_reimpl.py <QuantExt/test/stoplightbounds.cpp> 400000 42` → `overlap_stoplight_reimpl.out`

## Revalidation

1. **Order-statistic shift:**
   - Diff `include/boost/accumulators/statistics/tail_quantile.hpp` (the `std::ceil(cnt * (... 1. - p))` expression) and `historicalsimulationvar.cpp` `var()`.
   - Run `python3 support/var_backtest_exact.py` and inspect the last table.
   - On a built ORE, feed 500 P&Ls `1..500` and request `p = 0.99`. The shift is present if the result is 495 (the 6th largest).
2. **ES column semantics:** run `support/ore_hsvar_golden_check.py` against the current `Examples/MarketRisk/ExpectedOutput/HistSimVar/` files. Any change in `expectedShortfall()`'s `<=` predicate or in the example's requested quantiles shows up as a nonzero discrepancy.
3. **Traffic-light arithmetic:** `support/var_backtest_exact.py` must reproduce MAR99 Tables 1 and 2. If MAR99 changes, diff the table text at the same URL.
4. **ORE stop-light code:** diff `stoplightbounds.cpp` lines 164–197 (iid) and 99–162 (Monte Carlo). Rerun `support/overlap_stoplight_reimpl.py` with the updated test file, which parses the table from source.
5. **Placeholder and fallback:** check whether `varbacktest.hpp` still comments out its class, and whether `parametricvar.cpp` still falls back without the `samples` checks.
6. **Guidance currency:** check the Federal Reserve model-risk guidance page for letters superseding SR 26-2, and re-read MAR32.5/32.18/32.19 and MAR33.3 for parameter changes.

The toy Christoffersen numbers characterise the tests at `N = 250` only. Rerun with other seeds or `N` to check stability; do not reuse them as statements about real exception sequences.
