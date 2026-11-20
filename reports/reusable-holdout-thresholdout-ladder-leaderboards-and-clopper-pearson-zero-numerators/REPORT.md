# Reusable Holdout Guarantees, Small-Sample Binomial Intervals, and Negative-Instance Witnesses

## Summary

Reusing a held-out evaluation set of size $n$ across $k$ **adaptive** queries—where each candidate tool, law set, or patch is chosen after observing held-out feedback on prior candidates—destroys the classical non-adaptive Hoeffding scaling $n = O(\ln(k/\beta)/\tau^2)$. Releasing even **coarse scalar binary pass/fail counts** $c \in \{0, \dots, n\}$ permits an efficient majority-vote boosting attack (Blum and Hardt 2015, Theorem 5.1; Feldman, Frostig, and Hardt 2019) with empirical-minus-population bias $\Theta(\sqrt{k/n})$, saturating a $12$-instance held-out corpus in a dozen queries ($+0.239$ empirical bias at $k=12$, $+0.401$ at $k=50$ in seeded trials). Information-limiting gatekeepers restore logarithmic query scaling—**`Thresholdout`** (Dwork et al. 2015) answers $m$ adaptive queries with up to $B$ training-overfit hits when $n = \tilde{O}(\sqrt{B}\ln^{3/2}(m/\beta)/\tau^2)$, and **`The Ladder`** (Blum and Hardt 2015) bounds leaderboard error by $O(\log^{1/3}(kn)/n^{1/3})$ via a monotone step threshold $\eta = \Theta(n^{-1/3}\log^{1/3}(kn))$—but **require large $n$**: `Thresholdout`'s Laplace noise constant ($96 \ln(4m/\beta)$) is vacuous ($\tau > 1$) below $n \sim 10^3\text{–}10^4$, and `The Ladder`'s quantization step at $n = 12$ is $\eta = 12^{-1/3} = 0.437$. Consequently, small held-out corpora ($n \lesssim 30$) support **only single-shot pre-registered evaluation ($k = 1$)** or **`SparseValidate(m, B)`** binary gates (inflating failure probability $\beta$ by $\sum_{j=0}^B \binom{m}{j} \le m^B$ with zero noise).

Even at $k = 1$, zero observed failures ($0/n$) license only an upper bound on the population defect rate: at $n = 12, \alpha = 0.05$, one-sided Clopper–Pearson gives $[0, 0.2209]$ (Hanley–Lippman-Hand Rule-of-Three $3/n = 0.2500$), two-sided Clopper–Pearson gives $[0, 0.2646]$ ($\inf_p \text{Cov} = 0.9545$), and Wilson gives $[0, 0.2425]$ ($\inf_p \text{Cov} = 0.8392$, $\mathbb{E}_p[\text{Cov}] = 0.9538$). Direct inspection of `statsmodels/stats/proportion.py` (`ba594f9389e259cd9e19c26351332e43f33d9aa2`) uncovers two concrete boundary defects: (1) `method="jeffreys"` (lines 306–308) omits Brown, Cai, and DasGupta's (2001) boundary clamp $L_J(0) = 0$, returning a strictly positive lower bound (`4.01e-5` at $n=12$) that drives exact coverage to `0.0000` near $p = 0$; and (2) `method="binom_test"`'s conservative upper-bound fallback (line 270) subtracts instead of adding `(upper_bnd - val) / 2**power`. Furthermore, unstratified cryptographic-hash splitting of a corpus into design and held-out halves leaves a rare instance family of size $m$ with **zero held-out coverage** with probability $2^{-m}$ ($25.0\%$ for $m=2$, $12.5\%$ for $m=3$; $50.0\%$ and $25.0\%$ two-sided), whereas **family-stratified block allocation** reduces empty-cell probability to `0` for all $m \ge 2$. Finally, mature verification, fuzzing, and code-repair benchmarks (`sosy-lab/benchexec`, `HexHive/magma`, `google/fuzzbench`, `SWE-bench/SWE-bench`) never credit bare binary rejection on negative instances: they enforce **subproperty-tagged expected verdicts + machine-checked violation witnesses** (`SV-COMP`), **inline reached-vs-triggered fault canaries** (`Magma`) across $\ge 20\text{–}30$ trials with Mann–Whitney $U$ and Vargha–Delaney $\hat{A}_{12}$ tests (`FuzzBench`), and **non-empty suite execution + out-of-band exit-code checks** (`SWE-bench`).

---

## Applicability

This report synthesizes adaptive data analysis theory, exact binomial interval theory, and empirical benchmark-harness engineering across six pinned upstream repositories:

1. **`statsmodels/statsmodels`** (`ba594f9389e259cd9e19c26351332e43f33d9aa2`): `statsmodels/stats/proportion.py` (`proportion_confint` and helper search routines).
2. **`sosy-lab/benchexec`** (`efe409ce80754322fb7a754d5e0861997da8d2c9`): `benchexec/result.py`, `benchexec/runexecutor.py`, and `benchexec/model.py` (SV-COMP verdict and witness-validation scoring).
3. **`google/fuzzbench`** (`3234e151d70f6093272a9b4155e68ee57faf986c`): `analysis/stat_tests.py` and `analysis/experiment_results.py`.
4. **`HexHive/magma`** (`75d1ae7b180443a778b8830c79176ca5f93642ac`): ground-truth bug-reaching vs. bug-triggering canary architecture (Hazimeh et al. 2020).
5. **`SWE-bench/SWE-bench`** (`02e7a74ffd0b707aab73d203fe87bdc7c76afc8e`): `swebench/harness/grading.py` and `swebench/harness/run_evaluation.py`.
6. **`modestyachts/ImageNetV2`** (`0b0c3fe89058e4c7ee2348938b3f4f706a931bf3`): fresh matched-distribution holdout construction and near-duplicate removal (`README.md`, Recht et al. 2019).

Statistical bounds assume i.i.d. sampling of $n$ evaluation instances (or independent stratified blocks) from a target population distribution $\mathcal{D}$ over bounded per-instance queries $\varphi : \mathcal{X} \to [0, 1]$. When corpora consist of hand-crafted adversarial and honest litmus instances rather than i.i.d. draws from a natural distribution, binomial intervals apply only to a well-defined hypothetical super-population or randomized mutation generator; deterministic finite-population hypergeometric and witness-adequacy rules govern the fixed suite itself.

---

## Findings

### 1. Adaptive Holdout Reuse: Query Scaling, Step Leaderboards, and Coarse Pass/Fail Leakage

`Basis: normative + documentation + execution + derived`

#### 1.1 Comparative Guarantees of Holdout Release Mechanisms

Let $S_h \sim \mathcal{D}^n$ be a held-out set of $n$ instances, let $\varphi_1, \dots, \varphi_k : \mathcal{X} \to [0, 1]$ be queries chosen **adaptively** (where $\varphi_t$ depends arbitrarily on the answers $a_1, \dots, a_{t-1}$ returned on previous rounds), and write $E_{S_h}[\varphi] := \frac{1}{n}\sum_{i=1}^n \varphi(x_i)$ and $\mathcal{D}[\varphi] := \mathbb{E}_{x \sim \mathcal{D}}[\varphi(x)]$.

| Mechanism | Feedback Released per Query $\varphi_t$ | Generalization / Leaderboard Error $\tau$ ($1-\beta$ whp) | Max Adaptive Queries $k$ Supported at Fixed $(n, \tau)$ | Small-Sample Usability ($n \in [6, 30]$) |
| :--- | :--- | :--- | :--- | :--- |
| **Non-Adaptive Baseline** (Pre-registered $k$ queries) | Exact $E_{S_h}[\varphi_t]$ (all $\varphi_t$ fixed **before** touching $S_h$) | $\tau = \sqrt{\frac{\ln(2k/\beta)}{2n}}$ (Hoeffding + union bound) | $k \le \frac{\beta}{2}\exp(2n\tau^2)$ (**exponential in $n$**) | **Usable for $k=1$–$5$** ($\tau \approx 0.35$ at $n=12, k=1, \beta=0.05$) |
| **Naïve Adaptive Raw Score / Binary Pass Count** ($m=2$) | Exact pass count $c_t \in \{0, \dots, n\}$ (or rounded to $\alpha \le n^{-1/2}$) | **$\Theta\big(\sqrt{k/n}\big)$** (Blum–Hardt Thm 5.1; Hoeffding union $\sqrt{\frac{k\ln(n+1)+\ln(2/\beta)}{2n}}$) | **$k = O(n\tau^2)$** (**linear in $n$**; saturates completely at $k \approx n$) | **Catastrophic**: at $n=12$, $k=5$ already yields $+0.152$ bias; $k=12$ yields $+0.239$ |
| **Coarse $m$-Class Accuracy Count** (Feldman–Frostig–Hardt 2019) | Scalar 0–1 accuracy $\frac{1}{n}\sum \mathbf{1}[\hat{y}_i = y_i]$ over $y_i \in [m]$ | Upper: $\tilde{O}\big(\max\{\sqrt{\frac{k\log n}{mn}}, \frac{k}{n}\}\big)$; Eff. attack: $\Omega\big(\sqrt{\frac{k}{m^2 n}}\big)$ | **$k = \tilde{\Omega}(m n \tau^2)$** (up to $m^2\times$ longer lifespan for efficient attacks) | **No benefit at $m=2$** (accept/reject verifier corpora are binary!) |
| **`Thresholdout`** (Dwork et al. 2015, Lemma 24 & Thm 25) | $E_{S_t}[\varphi_t]$ if $|E_{S_h} - E_{S_t}| \le T + \gamma + \eta_t$; else $E_{S_h}[\varphi_t] + \xi_t$ (up to $B$ hits) | Pure DP: $n \ge \frac{192 B \ln(4k/\beta)}{\tau^2}$ ($T=\frac{3\tau}{4}, \sigma=\frac{\tau}{96\ln(4k/\beta)}$); Approx DP: $n = \tilde{O}\big(\frac{\sqrt{B}\ln^{3/2}(k/\beta)}{\tau^2}\big)$ | **$k \le \exp\big(\tilde{O}((n\tau^2/\sqrt{B})^{2/3})\big)$** (if overfit hits $\le B$; poly-time barrier $k = O(n^2)$ if $B=k$) | **Vacuous at small $n$**: $\sigma = \frac{\tau}{96\ln(4k/\beta)}$ requires $n \gtrsim 10^4$ before $\tau < 0.5$ |
| **`The Ladder`** (Blum & Hardt 2015, Thm 3.1) | Running best $R_t = \mathrm{round}_\eta(E_{S_h}[\ell_t])$ **only if** $E_{S_h}[\ell_t] < R_{t-1} - \eta$; else $R_{t-1}$ | $\mathrm{lberr} \le \varepsilon + \eta$ with $\Pr \le \exp(-2\varepsilon^2 n + (\lfloor 1/\eta\rfloor + 2)\ln(4k/\eta) + 1) \implies O\big(\frac{\log^{1/3}(kn)}{n^{1/3}}\big)$ | **$k \le \exp(O(n \tau^3))$** (**exponential in $n$**, deterministic, zero noise!) | **Too coarse below $n \approx 100$**: at $n=12$, $\eta = 12^{-1/3} = 0.437$ ($\le 2$ steps across $[0,1]$) |
| **`SparseValidate(k, B)`** (Dwork et al. 2015, Thm 27) | Single bit $\psi_t(S_h) \in \{0, 1\}$ ("did check fail?"); halts after $B$ ones | Per-query false-pass rate $\le \ell_t \beta_t$ where $\ell_t = \sum_{j=0}^{\min(t-1, B)} \binom{t}{j} \le k^B$ | Polynomial $k \le (\alpha / \beta_0)^{1/B}$ (for $B=1$ single-abort: $\ell_k = k + 1$) | **Only viable multi-check protocol at small $n$** (zero noise; $B=0$ or $1$ budget) |

#### 1.2 Why Releasing Only Coarse Pass/Fail Counts Fails to Protect Small Corpora

A widespread misconception in benchmark design is that hiding per-instance verdicts and releasing **only the total pass count** $c_t = \sum_{i=1}^n \mathbf{1}[f_t(x_i) = y_i] \in \{0, \dots, n\}$ prevents adaptive overfitting. Both theory and execution refute this:
1. **Blum–Hardt Majority-Vote Boosting Attack (Blum and Hardt 2015, Theorem 5.1 & Corollary 5.2):** Even when scores are rounded to $\alpha \le 1/\sqrt{n}$ (which holds for exact pass counts $c_t/n$ since $1/n \le 1/\sqrt{n}$ for every $n \ge 1$), an analyst who submits $k$ independent random labelings $u^{(1)}, \dots, u^{(k)} \in \{0, 1\}^n$ against a purely random target $y \sim \mathrm{Unif}(\{0, 1\}^n)$ (true accuracy $0.5000$), retains the subset $I^+ = \{t \in [k] : c_t/n > 1/2\}$, and outputs the coordinate-wise majority vote $u^*_i = \mathrm{maj}_{t \in I^+}(u^{(t)}_i)$ achieves empirical held-out accuracy $\frac{1}{2} + \Omega(\sqrt{k/n})$ with probability $\ge 2/3$ while population accuracy remains $0.5000$.
2. **Subset-Selection Overfitting of Law/Check Suites (Cawley and Talbot 2010):** In structural verification benchmarks where an author selects a *minimal law set* on a design split (dropping laws that appear redundant) or *retains every law that never failed* on honest design tools, selection variance acts identically to an adaptive query sequence over $2^L$ candidate subsets: a minimum set underfits unseen adversarial modes on held-out data, whereas a maximal non-failing set overfits accidental regularities of the design tools and rejects honest held-out tools.
3. **Why `ImageNetV2` Survived Reuse While Binary Suites Do Not:** Recht et al. (2019, `modestyachts/ImageNetV2`) rebuilt three 10,000-image held-out sets (`MatchedFrequency`, `Threshold0.7`, `TopImages`) and found a consistent $11\%\text{–}14\%$ accuracy drop attributable to distribution shift, **not** adaptive leaderboard overfitting (newer architectures beat older ones by wider margins on `ImageNetV2` than on original ImageNet!). Feldman, Frostig, and Hardt (2019, `arXiv:1905.10360`) proved why: with $m = 1,000$ classes and $n = 50,000$, efficient adaptive attacks degrade by $1/m$ to $\Omega(\sqrt{k/(m^2 n)})$, requiring $10^6\times$ more queries than binary ($m = 2$) pass/fail benchmarks.

---

### 2. Small-Sample Binomial Intervals, Zero Numerators ($k = 0$), `statsmodels` Source Audit, and Split Design

`Basis: normative + source + execution + derived`

#### 2.1 Exact vs. Approximate Intervals at Small $n$ and Zero Observed Failures ($k = 0$)

Given $k$ observed failures (or passes) in $n$ independent trials ($X \sim \mathrm{Binomial}(n, p)$) at nominal significance $\alpha = 0.05$ ($95\%$ confidence):

- **Clopper–Pearson Exact (`method="beta"`, Clopper and Pearson 1934):** Inverts two-tailed exact binomial tails via Beta quantiles (`statsmodels/stats/proportion.py:279-287`):
  $$L_{\mathrm{CP}}(k) = B\Big(\frac{\alpha}{2};\, k,\, n - k + 1\Big), \qquad U_{\mathrm{CP}}(k) = B\Big(1 - \frac{\alpha}{2};\, k + 1,\, n - k\Big)$$
  with $L_{\mathrm{CP}}(0) = 0$ and $U_{\mathrm{CP}}(n) = 1$. Guarantees $\inf_{p \in [0,1]} \Pr_p(p \in [L, U]) \ge 1 - \alpha$ everywhere, at the cost of conservatism. **Crucial boundary distinction at $k = 0$:** `proportion_confint(0, n, alpha=0.05, method="beta", alternative="two-sided")` puts $\alpha/2 = 0.025$ in the upper tail, yielding $U_{\mathrm{CP,2}}(0) = 1 - 0.025^{1/n} \approx 3.6889/n$ ($97.5\%$ actual coverage at $p \to U$), whereas `alternative="larger"` (one-sided upper bound `[0, ci_upp]`) uses $\alpha = 0.05$, yielding $U_{\mathrm{CP,1}}(0) = 1 - 0.05^{1/n} \approx 2.9957/n$—whose Taylor expansion gives **Hanley and Lippman-Hand's (1983) "Rule of Three" $3/n$**.
- **Wilson Score (`method="wilson"`, `proportion.py:296-305`):** Inverts $(k/n - p)^2 \le z_{\alpha/2}^2 p(1-p)/n$; at $k = 0$, $[0,\, \frac{z_{\alpha/2}^2}{n + z_{\alpha/2}^2}]$. Recommended by Brown, Cai, and DasGupta (2001) for mean coverage $\approx 1 - \alpha$, though worst-case coverage dips to `0.833–0.843` near $p \approx 1/(3n)$.
- **Agresti–Coull (`method="agresti_coull"`, `proportion.py:288-295,311-313`):** Adjusted Wald around $\tilde{p} = (k + z^2/2)/(n + z^2)$ clipped to $[0, 1]$; wider than Wilson at $k = 0$ and achieves $\inf_p \text{Cov} \in [0.900, 0.935]$ for $n \in [6, 50]$.
- **Jeffreys Equal-Tailed Prior (`Beta(1/2, 1/2)`):** Brown, Cai, and DasGupta (2001, §4.1.2, p. 108) define $L_J(k) = B(\alpha/2; k + \frac{1}{2}, n - k + \frac{1}{2})$ **with explicit boundary overrides $L_J(0) := 0$ and $U_J(n) := 1$**.

| Held-Out Size $n$ | CP 1-Sided $1 - 0.05^{1/n}$ | Rule of Three $3/n$ | CP 2-Sided (`beta`) $1 - 0.025^{1/n}$ | Wilson (`wilson`) | Agresti–Coull (`agresti_coull`) | `statsmodels` `jeffreys` (`[ci_low, ci_upp]`) | Wald (`normal`) |
| ---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| **`5`** | `0.4507` | `0.6000` | `0.5218` | `0.4345` | `0.4891` | `[0.0000934, 0.3794]` | `0.0000` |
| **`6`** | `0.3930` | `0.5000` | `0.4593` | `0.3903` | `0.4428` | `[0.0000785, 0.3304]` | `0.0000` |
| **`10`** | `0.2589` | `0.3000` | `0.3085` | `0.2775` | `0.3209` | `[0.0000479, 0.2172]` | `0.0000` |
| **`12`** | **`0.2209`** | **`0.2500`** | **`0.2646`** | **`0.2425`** | **`0.2820`** | **`[0.0000401, 0.1853]`** | `0.0000` |
| **`20`** | `0.1391` | `0.1500` | `0.1684` | `0.1611` | `0.1898` | `[0.0000242, 0.1166]` | `0.0000` |
| **`30`** | `0.0950` | `0.1000` | `0.1157` | `0.1135` | `0.1347` | `[0.0000162, 0.0797]` | `0.0000` |
| **`50`** | `0.0582` | `0.0600` | `0.0711` | `0.0713` | `0.0852` | `[0.0000098, 0.0488]` | `0.0000` |
| **`100`** | `0.0295` | `0.0300` | `0.0362` | `0.0370` | `0.0444` | `[0.0000049, 0.0247]` | `0.0000` |

**Takeaway for $n \le 12$:** Observing $0/12$ failures on a held-out set still admits a population failure rate up to **`22.1%` (one-sided $95\%$ Clopper–Pearson)** or **`26.5%` (two-sided)**. Even $0/6$ admits up to **`39.3%`–`45.9%`**. A dozen held-out instances can refute a broken claim when $k \ge 1$ failures occur, but cannot certify low defect rates ($< 5\%$).

#### 2.2 Two Source-Level Defects in `statsmodels/stats/proportion.py` (`ba594f9389e259cd9e19c26351332e43f33d9aa2`)

`Basis: source + execution`

1. **Missing Boundary Override in `method="jeffreys"` (`proportion.py:306-308`):**
   ```python
   elif method[:4] == "jeff":
       ci_low = stats.beta.ppf(alpha, count_a + 0.5, nobs_a - count_a + 0.5)
       ci_upp = stats.beta.isf(alpha, count_a + 0.5, nobs_a - count_a + 0.5)
   ```
   Unlike `method="beta"` (lines 282–287: `ci_low = 0 if q_ == 0 else ci_low`), `statsmodels` does **not** clamp `ci_low = 0` when `count == 0` (or `ci_upp = 1` when `count == nobs`). At $k = 0, n = 12, \alpha = 0.05$, `statsmodels` returns `ci_low = 4.01e-5 > 0`. For any true defect rate $p \in [0, 4.01 \times 10^{-5})$—including a genuinely sound checker with $p = 0$!—the outcome $X = 0$ occurs with probability $(1 - p)^{12} > 0.9995$, yet `0` lies **outside** `[ci_low, ci_upp]` (and $X \ge 1$ intervals have `ci_low >= beta.ppf(0.025, 1.5, 11.5) = 0.0177`), collapsing **exact frequentist coverage to `0.0000`** (`inf_p Cov = 0.0000` vs. `0.8972` for BCD's boundary-clamped Jeffreys).
2. **Sign-Inversion Bug in `method="binom_test"` Conservative Upper-Bound Search (`proportion.py:267-271`):**
   When `scipy.optimize.brentq` lands on a root `val` with slightly positive objective `func(val) = pvalue - alpha > 0`, `proportion.py` steps outward to bracket a conservative negative-`func` bound before bisection:
   ```python
   # Lower-bound branch (lines 254-257, correct):
   new_lb = val - (val - lower_bnd) / 2**power
   while func(new_lb) > 0 and power >= 0:
       power -= 1
       new_lb = val - (val - lower_bnd) / 2**power
   # Upper-bound branch (lines 267-270, sign bug on line 270):
   new_ub = val + (upper_bnd - val) / 2**power
   while func(new_ub) > 0 and power >= 0:
       power -= 1
       new_ub = val - (upper_bnd - val) / 2**power
   ```
   On line 270, `-` replaces `+`, stepping **downward below `val` toward `_q`** (where `pvalue == 1.0`, so `func(new_ub) = 1.0 - alpha > 0` for every iteration until `power = -1`), causing `_bisection_search_conservative(func, _q, new_ub)` at line 271 to raise `ValueError("problem with signs")` (`proportion.py:94`) whenever the initial $2^{-10}$ step is insufficient to clear `func > 0`.

#### 2.3 Stratified vs. Hashed Assignment of Instance Families to Splits

Suppose a benchmark of $N$ total instances contains a sub-property family $F$ of $m$ instances (for example, $m = 2$ or $3$ honest programs exercising a specific strict checker restriction inside $N = 12$ or $24$ total programs).
- **Unstratified Cryptographic Hash Split ($\text{digest}(\text{id}) \bmod 2 = 1$):** Assigns each instance independently with $p = 1/2$, so $\Pr(|F \cap S_h| = 0) = 2^{-m}$, and $\Pr(|F \cap S_h| = 0 \lor |F \cap S_d| = 0) = 2^{1-m}$ ($m \ge 1$). For $m = 2$, there is a **`25.0%` chance** that **zero** instances reach the held-out side and a **`50.0%` chance** that one side is empty; for $m = 3$, **`12.5%` / `25.0%`**. Across $C = 5$ distinct sub-property families of size $m = 3$ each, the probability that **at least one** sub-prediction is untestable on the held-out split is $1 - (1 - 0.125)^5 = \mathbf{48.7\%}$!
- **Unstratified Balanced Random Split ($|S_h| = N/2$):** Reduces $\Pr(|F \cap S_h| = 0) = \binom{N-m}{N/2}/\binom{N}{N/2}$ only marginally (`22.7%` at $N=12, m=2$; `9.09%` at $N=12, m=3$).
- **Family-Stratified Block Allocation + Cluster Integrity:** Partitioning instances by `(sub-property, expected-verdict)` stratum $s$ of size $m_s \ge 2$ and drawing $\lfloor m_s/2 \rfloor$ or $\lceil m_s/2 \rceil$ per stratum via a pre-registered seed guarantees $|F_s \cap S_h| \ge 1$ and $|F_s \cap S_d| \ge 1$ with **probability `1.0000`** (`0.00%` blind-spot rate). Conversely, syntactic variants derived from **one underlying bug or template** must share a **cluster ID** assigned intact to one side; splitting near-duplicate mutants across $S_d$ and $S_h$ leaks the bug template into design selection and invalidates binomial independence.

---

### 3. Negative-Instance Witnesses, Trial Repetition, and Contamination Detection Across Domains

`Basis: normative + source + execution`

#### 3.1 Establishing That Negative Instances Fail for the Intended Reason

A negative (adversarial or buggy) benchmark instance $x^-$ carries a **specific planted defect $d^*$**. A bare binary check `verdict(x^-) == REJECT` suffers from **masking**: a parser error, unrelated conservative over-approximation, environment crash, or wrong sanitizer fault scores as a "true rejection" while leaving the target check completely unexercised.

| Domain & Benchmark | Negative-Instance Expected Specification | Witness / Intended-Reason Verification Mechanism | Penalty / Handling of Wrong-Reason Rejection |
| :--- | :--- | :--- | :--- |
| **Software Verification**<br>`sosy-lab/benchexec` + SV-COMP Witness 1.0 / 2.0 | `ExpectedResult(False, subproperty)` (`benchexec/result.py:74-91,117-136`): `valid-deref`, `valid-free`, `valid-memtrack`, `no-overflow`, `unreach-call`, `no-data-race`, `termination` | Verifier must emit a **Violation Witness** (GraphML 1.0 error automaton or YAML 2.0 waypoint sequence of `assumption`/`branching` steps to `target` violation line), replayed by $\ge 2$ independent witness validators (`CPAchecker`, `Fshell-witness2test`, `Goblint`, `Symbiotic-Witch`) | Wrong subproperty (e.g. `false(no-overflow)` on `false(valid-deref)`) $\to$ `CATEGORY_UNKNOWN` (`0` pts, `result.py:347-358`); missing/unconfirmed witness $\to$ `CATEGORY_CORRECT_UNCONFIRMED` (`0` pts, `result.py:106,270`); wrong `true` $\to$ `-32` pts |
| **Fuzzing Evaluation**<br>`HexHive/magma` & Klees et al. (CCS 2018) | Front-ported historical CVEs with exact inline ground-truth fault predicate $P_{\text{bug}}$ | Source-level `MAGMA_LOG(bug_id, P_bug)` instrumentation separates three events per bug: **(1) Reached** (statement executed), **(2) Triggered** ($P_{\text{bug}}$ evaluated to `true`), **(3) Detected** (target terminated via crash/ASan) | Eliminates stack-hash and coverage-profile deduplication inflation (Klees et al. 2018 showed stack hashes overcount/merge distinct bugs by $2\times$–$10\times$); unrelated crash without `P_bug == true` credits `0` ground-truth bugs |
| **Repository Code Repair**<br>`SWE-bench/SWE-bench` (`grading.py`) | Issue-reproducing `FAIL_TO_PASS` (`F2P`) test IDs + regression `PASS_TO_PASS` (`P2P`) test IDs (`grading.py:195-206`) | Patch must flip **every** `F2P` test from fail to `PASSED`/`XFAIL` while maintaining **every** `P2P` test (`get_resolution_status`, L309–327), backed by three anti-bypass guards (`grading.py:31-46,101-109,166-175`) | **(1)** Empty `status_map` without non-zero `SUITE_RAN` match $\to$ `False` (blocks crashed browser/runner under `FAIL_ONLY`); **(2)** `SKIPPED` on `F2P` counts as `test_failed` (L108); **(3)** Non-zero `TEST_EXIT_CODE` with zero parsed failures rejects `conftest.py` stdout forgery (L166–175) |

#### 3.2 Repetition and Non-Parametric Statistical Testing Practices

- **Klees et al. (CCS 2018) & `google/fuzzbench` (`3234e151d70f6093272a9b4155e68ee57faf986c`, `analysis/stat_tests.py:52-215`):** Because randomized tools exhibit heavy-tailed run-to-run variance (Klees et al. documented median crash counts flipping from `1200 vs 800` on 1 run to `400 vs 1250` across `30` 24-hour runs, and `6h` rankings reversing at `24h`), `fuzzbench` enforces $N \ge 20\text{–}30$ independent trials per `(fuzzer, benchmark)` pair and computes:
  1. Pairwise two-sided and one-sided **Mann–Whitney $U$ tests** (`mannwhitneyu`, `stat_tests.py:52-64`) without normality assumptions;
  2. Multi-tool omnibus **Kruskal–Wallis** (`kruskal_test`, L118–124) and **Friedman** (`friedman_test`, L153–158) tests gated before **Holm–Bonferroni** (`p_adjust = 'holm'`, L108, 138) or **Nemenyi** (`posthoc_nemenyi_friedman`, L167) multiple-comparison adjustments;
  3. **Vargha–Delaney $\hat{A}_{12}$ non-parametric effect size** (`a12`, L171–206: $\hat{A}_{12} = \frac{2 R_1 - n_1(n_1 + 1)}{2 n_1 n_2}$, the probability a random run of tool 1 beats tool 2, with thresholds `> 0.556` small, `> 0.638` medium, `> 0.714` large).
- **`sosy-lab/benchexec` (`runexecutor.py`, Beyer et al. STTT 2019):** Enforces Linux `cgroups` v1/v2 CPU-core pinning, NUMA memory-bank binding, `MemorySwapMax=0`, overlay/container filesystem isolation, and wall/CPU timeout separation so deterministic verifiers do not suffer noisy-neighbor cross-talk.

#### 3.3 Detecting Test-Set Reuse, Leakage, and Pretraining Contamination

1. **Commit-Sealed Pre-Registration & One-Way Vault Evaluation:** Pre-registering exact hypothesis predicates, `FAIL_TO_PASS`/subproperty tags, and stratified split seeds by cryptographic digest before touching held-out instances bounds $|\mathcal{Y}| = 1$ in Dwork et al.'s Theorem 9.
2. **Fresh Distribution-Matched Holdout Reconstruction (`modestyachts/ImageNetV2`, `0b0c3fe89058e4c7ee2348938b3f4f706a931bf3`):** `README.md:90-138` details encrypting candidate and original image URLs inside identical 48-image MTurk HITs to match human selection-frequency histograms (`MatchedFrequency`), followed by 30-nearest-neighbor deduplication across **three metrics simultaneously** (raw-pixel $L_2$, pretrained VGG `fc7` feature $L_2$, and structural similarity `SSIM`) against both training and prior validation sets.
3. **Provable Black-Box Contamination Testing via Exchangeability (Oren et al., ICLR 2024, `arXiv:2310.17623`):** For language-model or agent benchmarks, an uncontaminated model treats exchangeable benchmark items identically under permutation, whereas pretraining memorization of a file's canonical repository ordering elevates the log-likelihood of the canonical order $\pi_0$ over random shuffles $\pi_1, \dots, \pi_{m-1}$. Comparing shard-summed log-probabilities across $m$ random permutations yields an **exact finite-sample $p$-value $p = \frac{1 + \sum_{j=1}^{m-1} \mathbf{1}[T(\pi_j) \ge T(\pi_0)]}{m}$** with guaranteed false-positive rate $\le \alpha$ without weight or training-data access, reliably detecting contamination on $1,000$-item test sets even down to $1.4\text{B}$ parameters and few-epoch exposure.
4. **Canary Strings and Temporal Cutoff Scrubbing:** Embedding unique GUID canary strings (e.g., BIG-bench / rolling post-cutoff GitHub issues) prevents accidental crawl ingestion and enables post-hoc corpus grep auditing.

---

### 4. Multi-Level Performance and Resource Footprint (`L1–L6`)

`Basis: source + documentation + execution + derived`

| Level | Metric / Dimension | Small-Sample Intervals (`statsmodels`) | Adaptive Holdout Gatekeepers (`Thresholdout` / `Ladder`) | Verification Harness (`benchexec` + SV-COMP Witness 2.0) | Fuzzing & Repair Suites (`FuzzBench` / `Magma` / `SWE-bench`) |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **L1: Authoring Velocity** | Instance & witness curation cost | `1` line API call; stratified split script ~`40` LoC | `Thresholdout` / `Ladder` gate `< 60` LoC; fresh `ImageNetV2`-style holdout costs hundreds of person-hours + MTurk budget | Adding an SV-COMP task + `.yml` property + baseline check: ~`15–60 min`/task; Witness 2.0 validator integration: `1–3` person-months | `Magma` front-porting + inline `MAGMA_LOG` canary per CVE: days/bug (`138` bugs across `9` targets); `SWE-bench_Verified` human filtering: ~`500` curated tasks from `2,294` |
| **L2: Toolchain Build Time** | Harness & container build latency | Pure Python (`scipy`/`statsmodels` wheel `< 2 s`) | Zero build cost (in-memory numpy/stdlib) | `benchexec` Python package `< 1 s`; building C/Java witness validators (`CPAchecker` JVM / `Symbiotic` LLVM): `2–15 min` | `SWE-bench` base+env+instance 3-layer Docker build: `2–15 min`/repo image; `Magma`/`FuzzBench` instrumented target build: `1–10 min`/target |
| **L3: Evaluation & Synthesis Latency** | Per-query / per-task execution wall time | Closed-form `beta`/`wilson`/`jeffreys`: **`2–15 µs`/call**; `binom_test` `brentq` root-find: **`0.3–2.5 ms`/call** | `O(n)` dot product per submission: **`< 50 µs`** for $n \le 10^5$ | SV-COMP verifier limit: **`900 s` (`15 min`)** CPU time; Witness 2.0 validator limit: **`90 s` (`10%`)** violation, **`300–900 s`** correctness | `FuzzBench` standard campaign: **`20–30` trials $\times$ `23–24 h`** (`200,000+` CPU-hours in Magma paper); `SWE-bench` per-instance test timeout: **`300–1,800 s`** |
| **L4: Runtime Execution Overhead** | Target instrumentation slowdown | N/A (post-hoc statistical summary) | Zero target runtime overhead | `benchexec` `cgroups` + `runexec` wrapper overhead **`< 0.5%`** CPU | `Magma` `MAGMA_LOG` atomic shared-memory canary overhead: **`< 1–3%`** throughput vs. ASan **`~2×`** slowdown |
| **L5: Witness / Receipt Verification Speed** | Verdict & certificate checking latency | Exact binomial grid audit (`2,000` $p$-points, $n \le 50$): **`< 15 ms`** in pure Python | Leaderboard step-update check: **`< 1 µs`**; Oren permutation test ($m=100$ shuffles, $1\text{K}$ items): `O(m)` forward passes | GraphML 1.0 XML automata parsing took `1–10 s` on multi-MB traces; **YAML Witness 2.0 waypoints parse in `< 50 ms`** before path replay | `SWE-bench` `get_eval_report` regex log + `TEST_EXIT_CODE` grading (`grading.py:329`): **`< 5 ms`/log** |
| **L6: RAM, Disk & Artifact Footprints** | Memory, container & witness byte sizes | `< 1 MiB` RAM (stdlib) or ~`65 MiB` RSS (`scipy`+`statsmodels`) | `< 1 MiB` state ($O(1)$ running `R_prev` in `Ladder`; $O(1)$ budget `B` in `Thresholdout`) | SV-COMP task cap **`15 GB` RAM**, **`2–4` CPU cores**; GraphML 1.0 witnesses reached **`10–100+ MB`**, reduced **`5–20×`** by YAML Witness 2.0 | `SWE-bench` Docker cache: **`100–600 GB`** disk across full suite (`~2–8 GB`/env image); `FuzzBench` corpus snapshots: **`1–20 GB`/campaign** |

---

### 5. Human Comprehensibility and Conceptual Simplicity (`C1–C2`)

`Basis: source + derived`

#### 5.1 `(C1)` Human Comprehensibility and Mental-Model Ergonomics

- **The "Zero Failures = Zero Risk" Cognitive Trap:** Human engineers and automated agents alike routinely misread `0 / 12 failures (100% pass)` as high-assurance validation, overlooking both the `22.1%–26.5%` Clopper–Pearson upper defect bound and `statsmodels`'s silent two-sided vs. one-sided tail halving (`alpha/2` vs. `alpha`). Reporting **explicit interval bounds `[0.0%, 22.1%] (95% 1-sided CP)` alongside `0/12`** replaces a misleading point estimate with an immediately legible sample-size horizon (Hanley and Lippman-Hand's $3/n$ mental rule requires **one division** in working memory!).
- **Witness Format Legibility (SV-COMP GraphML 1.0 vs. YAML 2.0):** Beyer et al. migrated SV-COMP from GraphML 1.0 XML control-flow automata to **YAML Witness 2.0** (`waypoint` sequences of source-line `location` + C-expression `constraint`) specifically because human developers could not audit 50,000-line XML state machines, whereas a 20-line YAML waypoint trace maps directly onto source lines and debugger watchpoints.

#### 5.2 `(C2)` Conceptual Simplicity, Orthogonality, and Universal Model Refinement

Across verification, fuzzing, and code-repair harnesses, ad-hoc bug-specific patches (`SUITE_RAN`, `SKIPPED` special cases, subproperty strings, `MAGMA_LOG` canaries) all enforce **one universal semantic invariant**:

> **Two-Point Differential Witness Principle:** Every negative benchmark instance $x^-$ is defined not merely by an input, but by a pair $(x^-, P_{d^*})$—or a minimal **honest twin $x^+$** differing only in the planted defect $d^*$—such that admission requires **(1) positive execution witness on $x^+$** (`PASS` + non-zero work proof) **and (2) fault-isolating rejection witness on $x^-$ identifying $d^*$** (`violation_id(x^-) == d^*`).

Under this single abstraction (Ousterhout deep module), `SWE-bench`'s `PASS_TO_PASS` + `FAIL_TO_PASS` + `SUITE_RAN`, `Magma`'s `reached` $\land$ `triggered` canary, and `SV-COMP`'s `false(subproperty)` + validated violation witness become **isomorphic projections of one schema**, eliminating silent pass-on-crash (`FAIL_ONLY` empty map) and wrong-reason rejection without per-runner special cases. Similarly, Dwork et al.'s **$\beta$-approximate max-information $I^\beta_\infty(S_h; A(S_h))$** (`arXiv:1506.02629`, Theorem 13) unifies differential privacy (`Thresholdout`) and description-length / monotone-step compression (`SparseValidate`, `The Ladder`, pre-registration) under one composition law ($I^{\beta_1+\beta_2}_\infty \le k_1 + k_2$).

---

### 6. End-to-End Solution and Implementation Validation (`V1–V4`)

`Basis: source + documentation + execution + derived`

- **`(V1)` Specification Adequacy, Mutation, and Non-Vacuity Validation:**
  - *Mutant Checker / Trivial-Oracle Rejection:* Every benchmark harness must be tested against adversarial degenerate submissions: (a) the **accept-all oracle**, (b) the **reject-all / constant-0 lobotomized oracle**, (c) a **crash-before-test runner** (`Executed 0 of 0`, `grading.py:28`), and (d) a **wrong-reason rejector** (rejecting every negative instance with a generic syntax/overflow error). Paired `(x^+, x^-)` twins + subproperty witness checks deterministically kill all four degenerate oracles (`100%` mutant-oracle kill rate). In code-repair benchmarks, `EvalPlus` (Liu et al. 2023) revealed that original HumanEval test suites failed to kill `11%–19%` of buggy LLM solutions until differential property-based input mutation expanded test density by $80\times$.
- **`(V2)` Harness, Validator, and Statistical-Library Differential Fuzzing:**
  - *Cross-Validator Witness Testing:* Since 2023, SV-COMP runs a dedicated **Competition on Witness Validation** (`benchexec/result.py:43-56,111-115`), scoring witness validators on both confirming valid witnesses and **refuting malformed/bogus witnesses** (`WITNESS_CATEGORY_WRONG`), catching unsoundness in validators themselves.
  - *Statistical Routine Differential Checking:* Comparing `statsmodels.stats.proportion.proportion_confint` against exact analytical identities and `scipy.stats.binomtest` immediately exposes both the `jeffreys` $k=0$ boundary omission (`proportion.py:306-308`) and the `binom_test` line-270 sign flip (`proportion.py:270`).
- **`(V3)` Concurrency, Crash, Container Isolation, and Nondeterminism Validation:**
  - Benchmark harnesses suffer false verdicts from container filesystem leakage, shared `/tmp` or network sockets, PID/clock races, and OOM kills masquerading as negative-test rejections. `sosy-lab/benchexec` (`runexecutor.py`) enforces kernel `cgroups` memory/swap ceilings, read-only bind mounts with disposable overlayfs layers, network-namespace disconnection (preventing live git-fetch leakage during `SWE-bench` evaluation!), and hardware performance-counter determinism; flaky concurrency benchmarks require `GenMC`/`Loom` schedule exploration or repeated seeded stress campaigns rather than single-run pass counts.
- **`(V4)` Drift Telemetry, Post-Deployment Fresh Holdouts, and Human Audit Validation:**
  - Static held-out sets inevitably decay through indirect ecosystem leakage (papers publishing failure analyses that shape subsequent architectures and prompts). Periodic **fresh-holdout replay** (`ImageNetV2`, rolling post-cutoff issue suites) paired with Oren et al.'s black-box canonical-order permutation monitor (`arXiv:2310.17623`) acts as a longitudinal `ModelPlex` validity monitor detecting when static benchmark scores decouple from true out-of-sample generalization.

---

## Boundaries

- **`known not to apply` — `Thresholdout` and Asymptotic `Ladder` Step Sizes on Very Small Corpora ($n \lesssim 30$):** Direct evaluation of Theorem 25 (`arXiv:1506.02629`, $\sigma = \tau/(96\ln(4m/\beta))$) and Theorem 3.1 (`arXiv:1502.04585`, $\eta \asymp n^{-1/3}$) establishes that neither mechanism enables fine-grained multi-round adaptive tuning on $10\text{–}20$ instances; small corpora must use **single-shot pre-registration ($k=1$)** or **freshly generated split instances** per iteration.
- **`known not to apply` — Treating Binomial Confidence Intervals as Bounds on Deterministic Adversarial Coverage:** Clopper–Pearson and Wilson intervals quantify sampling variance over i.i.d. draws from a fixed population $\mathcal{D}$; if an author hand-picks `12` easy test cases omitting an entire bug class, `0/12` bounds only the sampled sub-domain, **not** worst-case adversarial inputs outside $\mathrm{supp}(\mathcal{D})$.
- **`unsupported` — Small-Sample Multinomial `goodman` / `sison-glaz` Intervals at Zero Counts in `statsmodels`:** `multinomial_proportions_confint` (`statsmodels/stats/proportion.py:327-345`) explicitly documents that `method="goodman"` requires all cell counts $\ge 5$ and `method="sison-glaz"` requires $\ge 7$ categories, leaving zero-count small-sample multinomial cells unsupported without exact Dirichlet/Clopper–Pearson marginalization.
- **`not examined` — Randomized "Shaky Ladder" and Tight Multiclass Gap Closure:** Later randomized leaderboard refinements ($O(n^{-0.4})$ rate) and closing the theoretical gap between $\tilde{O}(\sqrt{k\log n/(mn)})$ and $\Omega(\sqrt{k/(m^2 n)})$ in Feldman, Frostig, and Hardt (COLT 2019 open problem) were not re-derived here.
- **`unknown` — Contamination Detection Power on Ultra-Small Test Sets ($n < 30$):** Oren et al. (`arXiv:2310.17623`) validated permutation-based contamination proofs down to $n = 1,000$ examples ($1.4\text{B}$ parameters); statistical power of canonical-order log-likelihood tests on micro-corpora of $n \le 20$ items in the presence of formatting noise remains unresolved.

---

## Evidence

### 1. Primary Repository Source Citations (Pinned 40-Hex Revisions)

- **`statsmodels/statsmodels` (`ba594f9389e259cd9e19c26351332e43f33d9aa2`):**
  - `statsmodels/stats/proportion.py`: `_bisection_search_conservative` (L63–111), `proportion_confint` docstring & `1 - alpha/2` boundary note (L114–181), two-sided `alpha = alpha / 2.0` halving (L216–218), `binom_test` root-finding & **line-270 sign bug** `new_ub = val - (upper_bnd - val) / 2**power` (L225–277), `beta` Clopper–Pearson with `q_ == 0` override (L278–287), `agresti_coull` & `wilson` (L288–305), **`jeffreys` omitting $k=0$ boundary clamp** (L306–308), `[0, 1]` clipping (L311–313).
- **`sosy-lab/benchexec` (`efe409ce80754322fb7a754d5e0861997da8d2c9`):**
  - `benchexec/result.py`: `CATEGORY_CORRECT` vs. `CATEGORY_CORRECT_UNCONFIRMED` (L20–25), `WITNESS_CATEGORY_*` (L43–56), `RESULT_FALSE_*` subproperties (L74–91), SV-COMP weights `+2/+1/0/-16/-32` (L103–115), `ExpectedResult` (L117–136), `_svcomp_score` & `get_result_category` enforcing subproperty agreement (L257–374).
- **`google/fuzzbench` (`3234e151d70f6093272a9b4155e68ee57faf986c`):**
  - `analysis/stat_tests.py`: `one_sided_u_test` & `two_sided_u_test` (L52–64), `kruskal_test` & `kruskal_posthoc_tests` with `p_adjust = 'holm'` (L118–150), `friedman_test` & `friedman_posthoc_tests` (L153–168), Vargha–Delaney `a12` with `0.556 / 0.638 / 0.714` thresholds (L171–206).
- **`SWE-bench/SWE-bench` (`02e7a74ffd0b707aab73d203fe87bdc7c76afc8e`):**
  - `swebench/harness/grading.py`: `SUITE_RAN` non-zero execution regex (L25–46), `TEST_EXIT_CODE_RE` (L51), `_resolve_case` documenting `676` truncated `SWE-bench_Verified` IDs (L61–82), `test_failed` counting `SKIPPED` as failure on `FAIL_TO_PASS` (L101–109), `get_logs_eval` anti-forgery exit-code cross-check (L155–176), `get_resolution_status` requiring `f2p == 1 and p2p == 1` (L309–327).
- **`modestyachts/ImageNetV2` (`0b0c3fe89058e4c7ee2348938b3f4f706a931bf3`):**
  - `README.md`: three 10,000-image splits `Threshold0.7`, `MatchedFrequency`, `TopImages` (L22–39), encrypted URL MTurk HIT pipeline (L90–115), 30-NN `l2`/`fc7`/`dssim` near-duplicate removal (L118–138).
- **`HexHive/magma` (`75d1ae7b180443a778b8830c79176ca5f93642ac`):**
  - Ground-truth front-ported CVE suite with inline reached/triggered canary instrumentation (Hazimeh, Herrera, and Payer 2020, `DOI: 10.1145/3428334`).

### 2. Primary Literature Citations

- C. J. Clopper and E. S. Pearson, *"The Use of Confidence or Fiducial Limits Illustrated in the Case of the Binomial,"* *Biometrika* 26(4):404–413, 1934 (`DOI: 10.1093/biomet/26.4.404`).
- James A. Hanley and Abby Lippman-Hand, *"If Nothing Goes Wrong, Is Everything All Right? Interpreting Zero Numerators,"* *JAMA* 249(13):1743–1745, 1983 (`DOI: 10.1001/jama.1983.03330370053031`).
- Lawrence D. Brown, T. Tony Cai, and Anirban DasGupta, *"Interval Estimation for a Binomial Proportion,"* *Statistical Science* 16(2):101–133, 2001 (`DOI: 10.1214/ss/1009213286`).
- Gavin C. Cawley and Nicola L. C. Talbot, *"On Over-fitting in Model Selection and Subsequent Selection Bias in Performance Evaluation,"* *JMLR* 11:2079–2107, 2010.
- Joseph P. Simmons, Leif D. Nelson, and Uri Simonsohn, *"False-Positive Psychology,"* *Psychological Science* 22(11):1359–1366, 2011 (`DOI: 10.1177/0956797611417632`).
- Cynthia Dwork, Vitaly Feldman, Moritz Hardt, Toniann Pitassi, Omer Reingold, and Aaron Roth, *"The Reusable Holdout: Preserving Validity in Adaptive Data Analysis,"* *Science* 349(6248):636–638, 2015 (`DOI: 10.1126/science.aaa9375`; full proofs in `arXiv:1506.02629`).
- Avrim Blum and Moritz Hardt, *"The Ladder: A Reliable Leaderboard for Machine Learning Competitions,"* *ICML 2015*, PMLR 37:1006–1014 (`arXiv:1502.04585`).
- Dirk Beyer et al., *"Witness Validation and Stepwise Testification across Software Verifiers,"* *ESEC/FSE 2015*, pp. 721–733 (`DOI: 10.1145/2786805.2786867`); *"Reliable Benchmarking: Requirements and Solutions,"* *STTT* 21(1):1–29, 2019 (`DOI: 10.1007/s10009-017-0469-y`).
- George Klees, Andrew Ruef, Benji Cooper, Shiyi Wei, and Michael Hicks, *"Evaluating Fuzz Testing,"* *ACM CCS 2018*, pp. 2123–2138 (`DOI: 10.1145/3243734.3243804`, `arXiv:1808.09700`).
- Vitaly Feldman, Roy Frostig, and Moritz Hardt, *"The Advantages of Multiple Classes for Reducing Overfitting from Test Set Reuse,"* *ICML 2019*, PMLR 97:1892–1900 (`arXiv:1905.10360`).
- Benjamin Recht, Rebecca Roelofs, Ludwig Schmidt, and Vaishaal Shankar, *"Do ImageNet Classifiers Generalize to ImageNet?,"* *ICML 2019*, PMLR 97:5389–5400 (`arXiv:1902.10811`).
- Ahmad Hazimeh, Adrian Herrera, and Mathias Payer, *"Magma: A Ground-Truth Fuzzing Benchmark,"* *POMACS* 4(3):49, 2020 (`DOI: 10.1145/3428334`, `arXiv:2009.01120`).
- Carlos E. Jimenez et al., *"SWE-bench: Can Language Models Resolve Real-World GitHub Issues?,"* *ICLR 2024* (`arXiv:2310.06770`).
- Yonatan Oren, Nicole Meister, Niladri Chatterji, Faisal Ladhak, and Tatsunori B. Hashimoto, *"Proving Test Set Contamination in Black-Box Language Models,"* *ICLR 2024* (`arXiv:2310.17623`).

### 3. Reproducible Execution Probes (`Basis: execution`)

1. **Interval Coverage, Split Blind-Spot, and Adaptive Boosting Probe (stdlib Python 3, acquired `2026-11-20`):**
   Evaluating the exact `statsmodels/stats/proportion.py` formulas (`ba594f9389e259cd9e19c26351332e43f33d9aa2`, L220–324) over a `2,000`-point + boundary $p$-grid (`1e-9` to `1 - 1e-9`) at $n = 12, \alpha = 0.05$ produced:
   - `beta` (2-sided CP): `k=0` `[0.0000, 0.2646]`, `inf_p Cov = 0.9545` (at $p = 0.724$), `E_p[Cov] = 0.9819`.
   - `wilson`: `k=0` `[0.0000, 0.2425]`, `inf_p Cov = 0.8392` (at $p = 0.0145$), `E_p[Cov] = 0.9538`.
   - `agresti_coull`: `k=0` `[0.0000, 0.2820]`, `inf_p Cov = 0.9221` (at $p = 0.462$), `E_p[Cov] = 0.9638`.
   - `jeffreys` (`statsmodels` unmodified): `k=0` `[0.0000401, 0.1853]`, `inf_p Cov = 0.0000` (at $p = 10^{-9}$), vs. BCD-clamped `jeffreys`: `inf_p Cov = 0.8972`, `E_p[Cov] = 0.9525`.
   - Seeded Blum–Hardt majority-vote simulation (`random.Random(20261119)`, `1,000` trials per $(n, k)$ against pure coin-flip labels `true_acc = 0.5000`): at $n = 12$, empirical accuracy of the boosted attack vector reaches **`0.6521` ($k=5$), `0.7390` ($k=12$), `0.8171` ($k=25$), and `0.9013` ($k=50$)**; at $n = 50$, **`0.6131` ($k=12$) and `0.7245` ($k=50$)**; at $n = 200$, **`0.5567` ($k=12$) and `0.6147` ($k=50$)** (`Basis: execution (simulation of Blum–Hardt boosting attack and Ladder algorithm)`).
2. **Direct Execution of Pinned `sosy-lab/benchexec/benchexec/result.py` (`efe409ce80754322fb7a754d5e0861997da8d2c9`):**
   Executing `benchexec.result.get_result_category` and `Property.compute_score` against an SV-COMP `CHECK( init(main()), LTL(G valid-deref) )` task with `ExpectedResult(False, "valid-deref")` yielded:
   ```text
   expected=false(valid-deref) | tool=false(valid-deref) | witness=correct -> eff_cat=correct             , svcomp_score=1
   expected=false(valid-deref) | tool=false(valid-deref) | witness=missing -> eff_cat=correct-unconfirmed , svcomp_score=0
   expected=false(valid-deref) | tool=false(no-overflow) | witness=correct -> eff_cat=unknown             , svcomp_score=0
   expected=false(valid-deref) | tool=false              | witness=correct -> eff_cat=unknown             , svcomp_score=0
   expected=false(valid-deref) | tool=true               | witness=correct -> eff_cat=wrong               , svcomp_score=-32
   ```

---

## Revalidation

To revalidate upstream implementations or audit a new held-out evaluation protocol:

1. **Re-Check `statsmodels` Boundary and Fallback Fixes (`< 5 s`):**
   Diff `statsmodels/stats/proportion.py` around lines 267–271 and 306–308, or run:
   ```bash
   python3 -c 'from statsmodels.stats.proportion import proportion_confint; print(proportion_confint(0, 12, 0.05, method="jeffreys"))'
   ```
   If the first tuple element is `> 0.0`, the missing BCD $k = 0$ boundary clamp remains present.
2. **Audit Any Small-Corpus Held-Out Protocol (4-Point Pre-Flight Gate):**
   - **Query-Count Check:** Confirm $k = 1$ (committed digest of checker/law-set before reading held-out results), or apply `SparseValidate(k, B)` / Bonferroni $\alpha / |\mathcal{H}|$ explicitly; reject any claim tuned iteratively against raw held-out pass counts when $k \gtrsim 0.1 n$.
   - **Stratification Check:** Group instances by `(sub-property, expected_verdict)` and verify $\min_s |F_s \cap S_h| \ge 1$ and zero shared mutation clusters across $S_d \cap S_h$.
   - **Interval Check:** Report exact one-sided or two-sided Clopper–Pearson bounds `[L, U]` alongside $c/n$ (never bare percentages or Wald intervals when $n < 50$ or $c \in \{0, n\}$).
   - **Witness-Reason Check:** Execute a negative-control oracle that rejects every input with a fixed dummy error code and assert that it scores **`0` true rejections** on the negative held-out suite.
