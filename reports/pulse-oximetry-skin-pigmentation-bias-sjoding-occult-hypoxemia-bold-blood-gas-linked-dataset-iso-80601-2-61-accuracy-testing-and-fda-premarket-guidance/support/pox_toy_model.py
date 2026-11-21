#!/usr/bin/env python3
"""TOY MODEL (synthetic numbers only; no patient or volunteer data).

Illustrates three arithmetic relationships used in the report. None of the outputs is a property
of any real oximeter, cohort, or standard test; parameters are arbitrary illustration values.

Part 1  ARMS identity: for paired differences d = SpO2 - SaO2,
        ARMS = sqrt(mean(d^2)) = sqrt(mean(d)^2 + sd_pop(d)^2)   (exact, sd with ddof=0).
Part 2  Pooled accuracy vs subgroup accuracy in a controlled-desaturation-like design:
        SaO2 plateaus uniform on [70, 100]; base error ~ N(0, s); a subgroup of fraction q has an
        additional bias D applied only when SaO2 < 80.  Analytic pooled ARMS^2 = s^2 + q*(1/3)*D^2;
        subgroup ARMS^2 = s^2 + (1/3)*D^2; checked by Monte Carlo.
Part 3  Occult-hypoxaemia fraction under a synthetic SaO2 distribution: P(SaO2 < 88 | 92 <= SpO2 <= 96)
        with SpO2 = round(SaO2 + b + e), e ~ N(0, s), SaO2 ~ N(93, 4) truncated to [70, 100].

Usage: python3 pox_toy_model.py <seed>
"""
import sys
import numpy as np

def main():
    rng = np.random.default_rng(int(sys.argv[1]))
    # Part 1
    print('# Part 1: ARMS identity on synthetic differences')
    for b, s in ((0.0, 2.0), (2.0, 2.0), (3.0, 1.0), (1.0, 3.5)):
        d = b + s * rng.standard_normal(200000)
        arms = np.sqrt(np.mean(d ** 2))
        ident = np.sqrt(np.mean(d) ** 2 + np.std(d) ** 2)
        print(f'bias={b} sd={s}: ARMS={arms:.4f} sqrt(mean^2+sd_pop^2)={ident:.4f} analytic sqrt(b^2+s^2)={np.hypot(b, s):.4f}')
    # Part 2
    print('# Part 2: pooled vs subgroup ARMS (uniform SaO2 70-100; extra bias D below 80 in subgroup fraction q)')
    print('s\tq\tD\tpooled_ARMS_analytic\tpooled_ARMS_mc\tsubgroup_ARMS_analytic\tsubgroup_bias_70_80')
    n = 400000
    for s in (1.5, 2.0, 3.0):
        for q in (0.15, 0.25):
            for D in (0.0, 2.0, 4.0, 6.0):
                sao2 = rng.uniform(70, 100, n)
                dark = rng.random(n) < q
                err = s * rng.standard_normal(n) + np.where(dark & (sao2 < 80), D, 0.0)
                pooled_mc = np.sqrt(np.mean(err ** 2))
                pooled_an = np.sqrt(s * s + q * D * D / 3)
                sub_an = np.sqrt(s * s + D * D / 3)
                print(f'{s}\t{q}\t{D}\t{pooled_an:.3f}\t{pooled_mc:.3f}\t{sub_an:.3f}\t{D:.1f}')
    # Part 3
    print('# Part 3: P(SaO2<88 | 92<=SpO2<=96), SaO2 ~ N(93,4) truncated [70,100]')
    print('bias_b\tsd_s\tP_occult\tratio_vs_b0')
    n = 2000000
    sao2 = rng.normal(93, 4, n * 2)
    sao2 = sao2[(sao2 >= 70) & (sao2 <= 100)][:n]
    for s in (1.5, 3.0):
        base = None
        e = rng.standard_normal(sao2.size)
        for b in (0.0, 1.0, 2.0, 3.0):
            spo2 = np.clip(np.round(sao2 + b + s * e), 0, 100)
            sel = (spo2 >= 92) & (spo2 <= 96)
            p = np.mean(sao2[sel] < 88)
            base = p if b == 0.0 else base
            print(f'{b}\t{s}\t{p:.4f}\t{p / base:.2f}')

if __name__ == '__main__':
    main()
