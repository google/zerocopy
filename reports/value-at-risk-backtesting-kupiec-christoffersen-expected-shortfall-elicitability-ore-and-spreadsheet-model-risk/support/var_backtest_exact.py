#!/usr/bin/env python3
"""Exact (non-simulated) backtesting arithmetic for coverage tests of a VaR
model, standard library only.

1. Reproduces Basel Framework MAR99 Table 1 (exact and type 1 / type 2
   probabilities for 250 independent observations) and Table 2 (cumulative
   probabilities and zone boundaries).
2. Emulates OpenSourceRisk/Engine QuantExt::stopLightBounds (iid branch):
   K = max(Q(s), 1) - 1 with Q(s) = smallest k with P(X <= k) >= s.
3. Kupiec (1995) proportion-of-failures likelihood-ratio test: exact finite
   sample size and power at N in {250, 500, 1000}, p = 0.01, nominal 5%.
4. Traffic-light zone probabilities under true exception rates 1%..5%.
5. Order statistic actually used as the empirical 99% VaR by
   (a) boost::accumulators tail_quantile<right> as called by ORE
       (n = ceil(N*(1-p)) evaluated in IEEE double), and
   (b) QuantLib GeneralStatistics::percentile(1-p) as called by
       GenericRiskStatistics::valueAtRisk (first k with k >= (1-p)*N),
   versus the exact-arithmetic index ceil(N*(1-p)).
Usage: python3 var_backtest_exact.py
"""
import math
from fractions import Fraction


def binom_pmf(n, k, p):
    return math.comb(n, k) * p ** k * (1 - p) ** (n - k)


def binom_cdf(n, k, p):
    return sum(binom_pmf(n, i, p) for i in range(0, k + 1))


def table1_table2():
    n = 250
    print('== MAR99 Table 1 reproduction (N=250): exact P(X=k) and type1 = P(X>=k) at 99%;'
          ' type2 = P(X<k) at 98/97/96/95%')
    print(' k | 99% exact  type1 | 98% exact type2 | 97% exact type2 | 96% exact type2 | 95% exact type2')
    for k in range(0, 16):
        row = [f'{k:2d}']
        e = binom_pmf(n, k, 0.01)
        t1 = 1 - binom_cdf(n, k - 1, 0.01) if k > 0 else 1.0
        row.append(f'{100*e:5.1f}% {100*t1:6.1f}%')
        for p in (0.02, 0.03, 0.04, 0.05):
            e = binom_pmf(n, k, p)
            t2 = binom_cdf(n, k - 1, p) if k > 0 else 0.0
            row.append(f'{100*e:5.1f}% {100*t2:5.1f}%')
        print(' | '.join(row))
    print('== MAR99 Table 2 reproduction: cumulative P(X<=k), p=0.01, N=250')
    for k in range(0, 11):
        print(f'   k={k:2d} cum={100*binom_cdf(n, k, 0.01):.2f}%')


def ore_iid_bounds(n, p_exc, levels):
    out = []
    for s in levels:
        k = 0
        while binom_cdf(n, k, p_exc) < s:
            k += 1
        out.append(max(k, 1) - 1)
    return out


def kupiec_lr(x, n, p):
    phat = x / n
    def ll(q):
        if q <= 0.0:
            return 0.0 if x == 0 else -math.inf
        if q >= 1.0:
            return 0.0 if x == n else -math.inf
        return (n - x) * math.log(1 - q) + x * math.log(q)
    return -2.0 * (ll(p) - ll(phat))


def kupiec_table(n, p=0.01, crit=3.841458820694124):
    accept = [x for x in range(0, n + 1) if kupiec_lr(x, n, p) <= crit]
    lo, hi = min(accept), max(accept)
    size = 1 - sum(binom_pmf(n, x, p) for x in accept)
    print(f'   N={n}: non-rejection region {lo} <= x <= {hi}; exact size at nominal 5% = {size:.4f}')
    for q in (0.02, 0.03, 0.04, 0.05):
        power = 1 - sum(binom_pmf(n, x, q) for x in accept)
        print(f'      true rate {q:.2f}: power = {power:.4f}')
    return lo, hi


def zone_probs(n=250):
    print('== Traffic-light zone probabilities (N=250, zones green 0-4, amber 5-9, red >=10)')
    for q in (0.01, 0.02, 0.03, 0.04, 0.05):
        g = binom_cdf(n, 4, q)
        a = binom_cdf(n, 9, q) - g
        r = 1 - g - a
        print(f'   true rate {q:.2f}: P(green)={g:.4f} P(amber)={a:.4f} P(red)={r:.4f}')


def var_index_emulation():
    print('== Order statistic (k-th largest loss) used as empirical 99% / 97.5% VaR')
    for n in (100, 250, 500, 715, 1000, 2000):
        for p in (0.99, 0.975):
            boost_n = math.ceil(n * (1.0 - p))  # ORE via boost tail_quantile<right>
            exact = math.ceil(Fraction(n) * (1 - Fraction(str(p))))
            # QuantLib percentile(1-p): first k (1-based ascending) with k >= (1-p)*N
            target = (1.0 - p) * n
            k = 1
            while k < target and k < n:
                k += 1
            print(f'   N={n:5d} p={p}: exact ceil(N(1-p))={exact:3d}  ORE/boost n={boost_n:3d}  '
                  f'QuantLib k={k:3d}  (1-p)*N in double={target!r}')


def main():
    table1_table2()
    print('== ORE stopLightBounds iid emulation (levels 0.95, 0.9999), p=0.01')
    for n in (250, 500, 1000):
        print(f'   N={n}: bounds (max green, max amber) = {ore_iid_bounds(n, 0.01, [0.95, 0.9999])}')
    print('== Kupiec POF LR test (chi2_1 critical value 3.8415), p=0.01')
    for n in (250, 500, 1000):
        kupiec_table(n)
    zone_probs()
    var_index_emulation()


if __name__ == '__main__':
    main()
